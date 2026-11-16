-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_10
-- name    : BlockSSM.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:05:03.786612+00:00
-- url     : https://prove2.me/theorems/6a22d154-14c9-4841-b6a0-6151f8b62621
-- title:
--   Theorem 10 — prototype decoding
-- statement:
--   Let $G$ be a finite group with $D_b(G)<\infty$. Then some optimal tracker has a rigid geometric form. Precisely, there are a one-layer tracker $T$ with blocks of size at most $b$, a finite group $H$ with a surjection $\phi:H\twoheadrightarrow G$, a faithful representation $\rho$ of $H$ on the state space $\mathbb C^n$ of $T$ that acts block by block and has all irreducible degrees at most $b$, and a vector $v\in\mathbb C^n$, such that:
--
--   1. $T$ tracks $G$, is finite-state, and its hidden dimension equals $n_b(G)$;
--   2. every bias is zero and every block $A^{(i)}_g$ is unitary;
--   3. $h_0=v$ and every transition $f_g$ equals $\rho(h)$ for some $h\in H$ with $\phi(h)=g$;
--   4. the decoder is **nearest-prototype** on the orbit $P=\{\rho(h)v:h\in H\}$: for every $z$, $\mathrm{dec}(z)=\phi(h)$ for some $h$ minimizing $\|z-\rho(h)v\|$;
--   5. if $G\neq1$, the separation
--   $$
--   \Delta_G=\min_{\phi(h)\neq\phi(h')}\|\rho(h)v-\rho(h')v\|
--   $$
--   is positive, decoding is correct on every open ball of radius $\Delta_G/2$ about a reachable state ($\|z-F_s(h_0)\|<\Delta_G/2$ implies $\mathrm{dec}(z)=\pi(s)$), and no deterministic decoder $\mathrm{dec}':\mathbb C^n\to G$ is correct on all closed balls of radius $\Delta_G/2$ about reachable states;
--   6. if $G=1$, the decoder is constant.
--
--   Norms are Euclidean. The theorem gives a quantitative readout guarantee for the optimal construction of the exact dimension theorem, and shows that the radius $\Delta_G/2$ cannot be improved.
--
--   Differences from the source:
--   - generalization: an integer block bound $b$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`), every value including $b=\infty$; reason: every integer bound is a case through the cast and $b=\infty$ is the unbounded case ($D_\infty$ of Definition 2); the argument is the same
--   - reading: "an optimal tracker has zero biases, unitary blocks, and a nearest-prototype decoder … for its orbit $P=\{\rho(h)v\}$" → there exist a finite-state tracking tracker of hidden dimension $n_b(G)$ and a cover $(H,\phi,\rho,v)$ with $\rho$ faithful, block-diagonal and admissible, $h_0=v$ and each $f_g=\rho(h)$ for a lift $h$ of $g$, satisfying all clauses; reason: "an optimal tracker" is existential (the universal reading fails: translating the state space keeps optimality but breaks zero biases), and "its orbit" refers to the cover data of the §3.1 construction, which the Lean statement names explicitly
--   - encoding: the norm $\|\cdot\|$ on $\mathbb C^n$ → the Euclidean distance `l2dist`, written coordinatewise; reason: Mathlib's default norm on the product type is the sup norm; the paper's norm is Euclidean
--   - encoding: $\Delta_G=\min_{\phi(h)\neq\phi(h')}\|\rho(h)v-\rho(h')v\|>0$ → a real $\Delta>0$ attained by a pair with $\phi(h)\neq\phi(h')$ and bounded above by every such distance; reason: this pins $\Delta$ as the minimum without a real `sInf`
--   - encoding: correctness on the open ball about a reachable state → for every word $s$ and every $z$ with $\|z-F_s(h_0)\|<\Delta/2$, $\mathrm{dec}(z)=\pi(s)$; reason: the correct label of the reachable state $F_s(h_0)$ is $\pi(s)$, well defined since $T$ tracks $G$
--   - encoding: $G\neq1$ and $G=1$ → `Nontrivial G` and `Subsingleton G`; reason: the same dichotomy
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 10, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_BlockSSM_trackerDim
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_BlockSSM_Supplement_l2dist

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 10 (Prototype decoding).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 10, p.5 (PDF p.6): "When D_b(G) < ∞, an
optimal tracker has zero biases, unitary blocks, and a nearest-prototype decoder. If G ≠ 1, define
for its orbit P = {ρ(h)v : h ∈ H} Δ_G = min_{ϕ(h)≠ϕ(h′)} ‖ρ(h)v − ρ(h′)v‖ > 0. Decoding is correct
on every open ball of radius Δ_G/2 about a reachable state. No deterministic decoder is correct on
all corresponding closed balls of radius Δ_G/2. For G = 1, decoding is constant and no separation
parameter is needed."

There is a tracker `T` that tracks `G`, is finite-state and has the minimum hidden dimension
`n_b(G)`, together with a finite cover `ϕ : H ↠ G`, a faithful representation `ρ` of `H` on the
state space of `T` that respects its block partition and has all irreducible degrees at most `b`,
and a vector `v`, such that: every bias is zero; every block `A_g^{(i)}` is unitary; `h₀ = v` and
every transition `f_g` is `ρ(h)` for a lift `h` of `g`; the decoder is nearest-prototype on the
orbit `P` (it returns `ϕ(h)` for an `h` minimizing `‖z − ρ(h)v‖`); for `G ≠ 1` the minimum
`Δ_G` is positive, decoding is correct on every open ball of radius `Δ_G/2` about a reachable state
`F_s(h₀)` (label `π(s)`), and every decoder `dec'` fails somewhere on a closed ball of radius
`Δ_G/2` about a reachable state; for `G = 1` the decoder is constant.

**Formalization Note.** Distances are Euclidean (`l2dist`). "An optimal tracker" is existential.
`Δ_G` is pinned as the minimum: attained by a pair with `ϕ(h) ≠ ϕ(h′)` and a lower bound for all
such pairs. "Respects the block partition": each `ρ(h)` acts block by block by a matrix. -/
theorem theorem_10 (G : Type u) [Group G] [Finite G] (b : ℕ∞) (hD : coverDim G b < ⊤) :
    ∃ (T : Tracker G b) (H : Type) (_ : Group H) (_ : Finite H) (φ : H →* G)
      (ρ : Representation ℂ H (State T.n)) (v : State T.n),
      T.Tracks ∧ T.IsFiniteState ∧ (T.hiddenDim : ℕ∞) = trackerDim G b ∧
      (∀ g, T.c g = 0) ∧ (∀ g i, T.A g i ∈ Matrix.unitaryGroup (Fin (T.n i)) ℂ) ∧
      Function.Surjective φ ∧ Function.Injective ρ ∧ IrrepDegreesLE ρ b ∧
      (∀ h, ∃ M : ∀ i, Matrix (Fin (T.n i)) (Fin (T.n i)) ℂ,
        ∀ (x : State T.n) i, ρ h x i = (M i).mulVec (x i)) ∧
      T.h₀ = v ∧ (∀ g, ∃ h, φ h = g ∧ ∀ x, T.step g x = ρ h x) ∧
      (∀ z, ∃ h, T.dec z = φ h ∧ ∀ h', l2dist z (ρ h v) ≤ l2dist z (ρ h' v)) ∧
      (Nontrivial G → ∃ Δ : ℝ, 0 < Δ ∧
        (∃ h h', φ h ≠ φ h' ∧ l2dist (ρ h v) (ρ h' v) = Δ) ∧
        (∀ h h', φ h ≠ φ h' → Δ ≤ l2dist (ρ h v) (ρ h' v)) ∧
        (∀ (s : List G) (z : State T.n),
          l2dist z (T.wordMap s T.h₀) < Δ / 2 → T.dec z = wordProd s) ∧
        (∀ dec' : State T.n → G, ∃ (s : List G) (z : State T.n),
          l2dist z (T.wordMap s T.h₀) ≤ Δ / 2 ∧ dec' z ≠ wordProd s)) ∧
      (Subsingleton G → ∀ z z', T.dec z = T.dec z') := by sorry

end BlockSSM.Supplement
