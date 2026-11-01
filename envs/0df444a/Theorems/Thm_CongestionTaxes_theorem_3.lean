-- Prove2me | Theorems.Thm_CongestionTaxes_theorem_3
-- name    : CongestionTaxes.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:08.685236+00:00
-- url     : https://prove2.me/theorems/aff06aa2-41c7-4875-aefa-d11a4ffdb528
-- title:
--   Theorem 3 — taxes from the Poisson relaxation have price of anarchy at most $\sup_{\ell\in\mathcal L}\rho_\ell$
-- statement:
--   Let $\mathcal L$ be a set of resource costs $\ell:\mathbb N\to\mathbb R_{>0}$ (extended by $\ell(0)=0$) satisfying Assumption 1, with
--
--   $$
--   \rho=\sup_{\ell\in\mathcal L}\rho_\ell<\infty,\qquad \rho_\ell=\sup_{x\in\mathbb N}\frac{\mathbb E_{P\sim\mathrm{Poi}(x)}[P\ell(P)]}{x\ell(x)},
--   $$
--
--   and consider all congestion games whose resource costs lie in $\mathcal L$, with any number of agents and resources. For each such game $G$ let (12) be the convex program minimizing $\sum_r p_r(v_r)$, $p_r(v)=\mathbb E_{P\sim\mathrm{Poi}(v)}[P\ell_r(P)]$, over the expected loads $v_r$ of mixed profiles $y$. A taxation mechanism of Definition 4 is given by choosing for every game a parameter vector $(v_r)_r$; resource $r$ then charges $\tau_r(x,v_r)=f_r(x,v_r)-\ell_r(x)$ to each of its $x$ users. Then:
--
--   1. **(A)** for every game of the class, program (12) has a solution;
--   2. **(B)** for every mechanism that uses, on every game of the class, the parameter vector $\bar v$ of some solution $(\bar y,\bar v)$ of (12): all taxes are nonnegative, every game of the class has a pure Nash equilibrium under the taxes, and the price of anarchy is at most $\rho$ for pure Nash, mixed Nash, correlated and coarse correlated equilibria;
--   3. **(C)** for every $\varepsilon>0$ there is a precision $\xi>0$, depending only on $\varepsilon$ and $\mathcal L$, such that every mechanism using, on every game of the class, the parameters of a $(1+\xi)$-approximate solution of (12) has nonnegative taxes, admits a pure Nash equilibrium on every game of the class, and has price of anarchy at most $\rho+\varepsilon$ for all four equilibrium classes.
--
--   By Theorem 1 of the paper (not part of this statement), $\rho$ is also the NP-hardness threshold for approximating the minimum social cost, so these taxes match the best approximation a polynomial-time algorithm can achieve.
--
--   **Formalization Note** A mechanism is a selection of parameters for every game (agents $\{0,\dots,N-1\}$, resources $\{0,\dots,m-1\}$); the price of anarchy is taken in $[0,\infty]$ with $0/0=0$. No model of computation is formalized: the polynomial-time clause is read as (C).
--
--   Differences from the source:
--
--   - reading: for any $\varepsilon>0$ one can design in polynomial time, through the approximate solution of (12), a taxation mechanism with price of anarchy $\le\sup_\ell\rho_\ell+\varepsilon$ → (C): for every $\varepsilon>0$ there is $\xi>0$, depending on $\varepsilon$ and $\mathcal L$ only, such that every selection of $(1+\xi)$-approximate solutions of (12) gives price of anarchy $\le\sup_\ell\rho_\ell+\varepsilon$; reason: the paper fixes no model of computation for real-valued costs and the infinite series $p_r$; its proof (p.20) shows exactly (C), citing the polynomial-time solvability of convex programs, and a $\xi$ uniform in the game is what makes the precision a constant
--   - generalization: "denote with $(\bar y,\bar v)$ a solution of (12)" → clause (A): every game of the class has a solution of (12); reason: the theorem presupposes a solution; dropping (A) gives the printed statement
--   - generalization: the price-of-anarchy bounds → also nonnegativity of all taxes and existence of a pure Nash equilibrium under the taxes, in (B) and (C); reason: Definition 4 declares $\tau_r$ with values in $\mathbb R_{\ge0}$ (Lemma 1(a)), and footnote 3 makes the price of anarchy well defined through existence of pure equilibria
--   - encoding: the taxation mechanism with parameter vector $(\bar v_r)_r$; $\mathrm{PoA}(T)$ for any and all equilibrium classes (p.5) → all selections of parameters per game; a price of anarchy for each of the four classes, in $[0,\infty]$ with $0/0=0$; reason: solutions of (12) need not be unique, so every tie-break is covered; strategies may contain $\emptyset$, so $\mathrm{MinCost}=0$ is possible and then every equilibrium has social cost $0$
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
--   - encoding: agents endowed with feasible allocations $\mathcal A_i\subseteq2^{\mathcal R}$ → $\mathcal A_i$ nonempty in the class; reason: $\Delta(s_i)$ in (12) is empty otherwise
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Theorem 3, p.19; proof, pp.19–20

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rhoSup
import Definitions.Def_CongestionTaxes_tax
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_IsSolution
import Definitions.Def_CongestionTaxes_IsApproxSolution
import Definitions.Def_CongestionTaxes_InClass
import Definitions.Def_CongestionTaxes_EqClass
import Definitions.Def_CongestionTaxes_poa

open scoped ENNReal

namespace CongestionTaxes

/-- **Theorem 3** (Paccagnan, Gairing, *In Congestion Games, Taxes Achieve Optimal Approximation*,
arXiv:2105.07480v2, Theorem 3, p.19). Let `𝓛` be a set of resource costs satisfying Assumption 1
with `sup_{ℓ∈𝓛} ρ_ℓ < ∞`, and consider the congestion games with costs in `𝓛` (any number of agents
and resources). Then:

(A) for every such game the convex program (12) has a solution;

(B) (first bullet) for every mechanism `T` that uses, on every game `G` of the class, the
parameter vector `v̄ = T(G)` of a solution `(ȳ, v̄)` of (12): all taxes of Definition 4 are
nonnegative, every game of the class has a pure Nash equilibrium under the taxes, and the price of
anarchy of `T` is at most `sup_{ℓ∈𝓛} ρ_ℓ` for pure Nash, mixed Nash, correlated and coarse
correlated equilibria;

(C) (second bullet) for every `ε > 0` there is a precision `ξ > 0`, depending on `ε` and `𝓛` only,
such that every mechanism using, on every game of the class, the parameters of a
`(1 + ξ)`-approximate solution of (12) has nonnegative taxes, admits a pure Nash equilibrium on
every game of the class, and has price of anarchy at most `sup_{ℓ∈𝓛} ρ_ℓ + ε` for all four
equilibrium classes.

**Formalization Note** A mechanism is a selection `T N m G : Fin m → ℝ` of parameters per game,
since solutions of (12) need not be unique; the statement covers every selection. "In polynomial
time, through the approximate solution of (12)" is read as (C): the proof (p.20) shows that a
`(1 + ξ)`-approximate solution suffices, and the precision `ξ` is chosen before the game. No model
of computation is formalized. -/
theorem theorem_3 (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤) :
    (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
      ∃ y v, IsSolution G y v) ∧
    (∀ T : (N m : ℕ) → CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m) → Fin m → ℝ,
      (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
        ∃ y, IsSolution G y (T N m G)) →
      (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
        ∀ r x, 0 ≤ tax (G.latency r) x (T N m G r)) ∧
      (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
        ∃ a, CongestionPoA.AsymSum.IsPureNash (taxedGame G (T N m G)) a) ∧
      ∀ K : EqClass, poa K L T ≤ rhoSup L) ∧
    (∀ ε : ℝ, 0 < ε → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ T : (N m : ℕ) → CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m) → Fin m → ℝ,
        (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
          ∃ y, IsApproxSolution ξ G y (T N m G)) →
        (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
          ∀ r x, 0 ≤ tax (G.latency r) x (T N m G r)) ∧
        (∀ (N m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m)), InClass L G →
          ∃ a, CongestionPoA.AsymSum.IsPureNash (taxedGame G (T N m G)) a) ∧
        ∀ K : EqClass, poa K L T ≤ rhoSup L + ENNReal.ofReal ε) := by sorry

end CongestionTaxes
