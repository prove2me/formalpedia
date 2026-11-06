-- Prove2me | Theorems.Thm_ConeL2G_theorem_1_7
-- name    : ConeL2G.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:07.062647+00:00
-- url     : https://prove2.me/theorems/7846ce13-2eec-4213-bcbc-57a370a97665
-- title:
--   Theorem 1.7 (Main) — $D^2\succeq(1-\gamma)D$, and spectral gap $c_\alpha/n$ for lists of size $>\alpha\Delta$, $\alpha>\alpha^*\approx1.7408$
-- statement:
--   Let $G$ be a finite graph on $n$ vertices with color lists $(L_i)$, let $\mu$ be the uniform distribution on its proper list colorings, $D_i=I-P_i$, $D=\sum_iD_i$, and $\beta_\Delta=1-\big(\frac{s-1}{s}\big)^\Delta$.
--
--   1. There is an absolute constant $C>0$ such that, for every such $G$ whose degrees are at most $\Delta$, where $\Delta>1$ is an integer, every real $s\ge5$ with $|L_i|\ge s+\deg(i)$ for all $i$, and every $f$,
--   $$\big\langle f,D^2f\big\rangle_\mu\ \ge\ \Big(1-\sqrt{\frac{\Delta\beta_\Delta}{s}+\frac{C\Delta^2}{s^3}}\Big)\langle f,Df\rangle_\mu ,$$
--   that is, $D^2\succeq(1-\gamma)D$ with $\gamma=\sqrt{\Delta\beta_\Delta/s+C\Delta^2/s^3}$.
--   2. Let $\alpha^*\approx1.7408$ be the solution of $\alpha^*=2-\exp(-1/(\alpha^*-1))$ in $(1,\infty)$. For every $\alpha>\alpha^*$ there are $c_\alpha>0$ and $\Delta_0$ such that, for every $\Delta\ge\Delta_0$, every graph $G$ on $n$ vertices with degrees at most $\Delta$ and every lists with $|L_i|>\alpha\Delta$ for all $i$, the Glauber dynamics has spectral gap at least $c_\alpha/n$:
--   $$\frac{c_\alpha}{n}\langle f,f\rangle_\mu\le\big\langle f,\tfrac1nDf\big\rangle_\mu\qquad\text{for every } f \text{ with } \mathbb E_\mu f=0 .$$
--
--   The second clause improves the classical $2\Delta$ (Jerrum) and $11\Delta/6$ (Vigoda) thresholds for spectral-gap bounds on list colorings with lists of size proportional to $\Delta$.
--
--   **Formalization Note** $\alpha>\alpha^*$ is written $1<\alpha$ and $2-\exp(-1/(\alpha-1))<\alpha$: the map $\alpha\mapsto\alpha-2+\exp(-1/(\alpha-1))$ is strictly increasing on $(1,\infty)$ with limit $-1$ at $1^+$, and $\alpha^*$ is its unique zero.
--
--   Differences from the source:
--   - generalization: G with maximum degree ∆ > 1 (clause 1) and maximum degree ∆ (clause 2) → a natural number Δ (1 < Δ in clause 1, Δ ≥ Δ₀ in clause 2) bounding every degree; reason: adding a disjoint star with Δ leaves and long lists makes Δ the maximum degree without changing ⟨f, Df⟩, ⟨f, D²f⟩ or the variance of functions of the original vertices (µ is a product), so the bound for the enlarged graph gives the bound for G: in clause 1 directly, and in clause 2 the gap c/(n + Δ + 1) of the enlarged chain gives ⟨f, Df⟩_µ ≥ c Var_µ(f) for functions of the original vertices, i.e. gap c/n for G; Lean also covers Δ above the maximum degree, and it specializes to the source at Δ = the maximum degree
--   - encoding: D² ⪰ (1 − γ)D in L²(µ) → (1 − γ) ⟨f, Df⟩_µ ≤ ⟨f, D(Df)⟩_µ for every f; reason: Loewner order of self-adjoint operators is the order of their quadratic forms
--   - encoding: α > α* with α* = 2 − exp(−1/(α* − 1)) → 1 < α ∧ 2 − Real.exp (−1/(α − 1)) < α; reason: α − 2 + e^{−1/(α−1)} is strictly increasing on (1, ∞) with limit −1 at 1⁺, so its unique zero is α* and it is positive exactly for α > α*
--   - encoding: q > α∆ with q the minimum list size → α * Δ < |L i| for every i; reason: the minimum exceeds αΔ iff every list does
--   - encoding: spectral gap of the Glauber dynamics at least c_α/n, for sufficiently large ∆ → SpinGirth5.PoincareIneq µ (glauberLap G L) (c / n), with ∃ c > 0, ∃ Δ₀, ∀ Δ ≥ Δ₀ (c and Δ₀ depending on α only); reason: the spectral gap of a reversible chain is the best Poincaré constant; the constants are uniform over graphs and lists as in the paper
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Theorem 1.7, p.5

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_beta
import Definitions.Def_ConeL2G_glauberLap

open Finset

namespace ConeL2G

/-- **Theorem 1.7 (Main).** Li–Oveis Gharan, *Local-to-Global Theorems Based on Cones with
Applications to Graph Coloring*, arXiv:2610.37721, Theorem 1.7, p.5: "There exists an absolute
constant `C > 0` such that, whenever `s ⩾ 5` and `|Lᵢ| ⩾ s + deg(i)` for all `i ∈ G`, we have
`D² ⪰ (1 − √(∆β_∆/s + C∆²/s³)) D =: (1 − γ)D`.
Consequently, if `q > α∆` where `α > α*` for `α* = 2 − exp(−1/(α* − 1)) ≈ 1.7408` and sufficiently
large `∆`, the spectral gap of the Glauber dynamics is at least `c_α/n` for some constant `c_α > 0`."

Setting (p.1): `G = (V, E)` a finite graph with `n` vertices and maximum degree `∆ > 1`, lists
`{Lᵢ}`, `µ` uniform on proper list colorings (`unifMass G L`), `Dᵢ = I − Pᵢ`, `D = Σᵢ Dᵢ`
(`SpinGirth5.lapSum µ univ`), `(1/n)D` the Laplacian of the Glauber dynamics (`glauberLap G L`);
`q` is the minimum list size; `β_∆ = beta s ∆`.

**Formalization Note.**
1. Clause (i): `D² ⪰ (1 − γ)D` in `L²(µ)` is the quadratic-form inequality
   `(1 − γ)⟨f, Df⟩_µ ⩽ ⟨f, D(Df)⟩_µ` for every `f`. `C` is quantified before the graph, the lists,
   the palette `Fin K`, `∆` and `s`; `s` is real.
2. `∆` is a natural number `> 1` bounding every degree (the paper's maximum degree). Adding a
   disjoint star with `∆` leaves (lists large enough) makes `∆` the maximum degree without changing
   either side for functions of the original vertices, so this is the paper's statement.
3. Clause (ii): "`q > α∆`" is `α∆ < |Lᵢ|` for every `i`; "`α > α*`" is encoded as
   `1 < α ∧ 2 − exp(−1/(α − 1)) < α` (the map `α ↦ α − 2 + exp(−1/(α − 1))` is strictly increasing on
   `(1, ∞)` with limit `−1` at `1⁺`, and `α*` is its unique zero). `c_α` and the threshold `∆₀` depend
   on `α` only. "Spectral gap at least `c_α/n`" is the Poincaré inequality
   `SpinGirth5.PoincareIneq µ (glauberLap G L) (c_α/n)`. -/
theorem theorem_1_7 :
    (∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (K : ℕ) (L : V → Finset (Fin K)) (Δ : ℕ) (s : ℝ), 1 < Δ →
      (∀ i : V, G.degree i ≤ Δ) → 5 ≤ s → (∀ i : V, s + (G.degree i : ℝ) ≤ ((L i).card : ℝ)) →
      ∀ f : (V → Fin K) → ℝ,
        (1 - Real.sqrt ((Δ : ℝ) * beta s Δ / s + C * (Δ : ℝ) ^ 2 / s ^ 3)) *
            MarkovMixing.innerPi (unifMass G L) f (SpinGirth5.lapSum (unifMass G L) univ f) ≤
          MarkovMixing.innerPi (unifMass G L) f
            (SpinGirth5.lapSum (unifMass G L) univ (SpinGirth5.lapSum (unifMass G L) univ f))) ∧
    (∀ α : ℝ, 1 < α → 2 - Real.exp (-1 / (α - 1)) < α →
      ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (K : ℕ) (L : V → Finset (Fin K)),
          (∀ i : V, G.degree i ≤ Δ) → (∀ i : V, α * (Δ : ℝ) < ((L i).card : ℝ)) →
          SpinGirth5.PoincareIneq (unifMass G L) (glauberLap G L)
            (c / (Fintype.card V : ℝ))) := by sorry

end ConeL2G
