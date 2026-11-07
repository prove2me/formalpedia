-- Prove2me | Theorems.Thm_DynBrooks_lemma_4_7
-- name    : DynBrooks.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:47.551032+00:00
-- url     : https://prove2.me/theorems/0b2c7f5f-8ae2-4edd-96d3-b106b4878580
-- title:
--   Lemma 4.7 — colors surviving random proposals
-- statement:
--   Let $Q$ be a graph of maximum degree at most $K_0\Delta$, where $K_0$ is a fixed constant. Independently, each vertex becomes active with probability $p$ and proposes a uniformly random color from $[\Delta]$; an active vertex retains its color if no active neighbor proposes the same color. Let $U\subseteq V(Q)$ with $|U|\le\Delta$. For a sufficiently small constant $p>0$:
--
--   1. if $F$ is a collection of $q$ nonedges in $Q[U]$ with $q/\Delta\ge\ell$, then with probability at least $1-\exp(-\Omega(q/\Delta))$ there are $\Omega(q/\Delta)$ distinct colors, each retained by both endpoints of some nonedge in $F$;
--   2. if $|U|=m\ge\ell$, then with probability at least $1-\exp(-\Omega(m))$, at least $\Omega(m)$ distinct colors are retained by vertices of $U$.
--
--   Here $\ell\ge1$ and $\Delta\ge\ell^{10}$ are the standing assumptions of §4. The constants are ordered $K_0$, then $p_0$, then $p\in(0,p_0]$, then one $\Omega$-constant $c>0$.
--
--   Differences from the source:
--   - generalization: ℓ = max{1, ⌈log(n + T + 2)⌉} with ∆ ≥ ℓ^{10} (§4) → every natural number ℓ ≥ 1 with ∆ ≥ ℓ^{10}; reason: the paper's ℓ is one such value
--   - encoding: the product probability space → a finite sum over outcomes V → {inactive} ∪ [∆] with product weights; reason: the same law
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 4.7, p.23 (PDF 25); standing assumption §4.1, p.15 (PDF 17)

import Mathlib
import Definitions.Def_DynBrooks_Proposals

namespace DynBrooks

open Classical in
/-- **Lemma 4.7** (Colors surviving random proposals; Mishra, Mukherjee, *Fully Dynamic Brooks
Coloring*, STOC 2027 submission, sha256 6542a9f1…, p.23 (PDF 25)). Let `Q` be a graph of maximum degree
at most `K₀∆`, where `K₀` is a fixed constant. Independently, each vertex becomes active with probability
`p` and proposes a uniformly random color from `[∆]`; an active vertex retains its color if no active
neighbor proposes the same color. Let `U ⊆ V(Q)` with `|U| ≤ ∆`. For a sufficiently small constant
`p > 0`:
1. if `F` is a collection of `q` nonedges in `Q[U]` with `q/∆ ≥ ℓ`, then with probability at least
   `1 − exp(−Ω(q/∆))` there are `Ω(q/∆)` distinct colors, each retained by both endpoints of some
   nonedge in `F`;
2. if `|U| = m ≥ ℓ`, then with probability at least `1 − exp(−Ω(m))`, at least `Ω(m)` distinct colors are
   retained by vertices of `U`.

**Formalization Note.** Order of constants: `K₀`, then the threshold `p₀`, then `p ∈ (0, p₀]`, then one
constant `c > 0` for all four `Ω`. The probability space is the finite product law of `proposalProb`
(colors `Fin ∆` stand for `[∆]`). `ℓ` enters through §4's standing assumptions `ℓ ≥ 1` and `∆ ≥ ℓ^{10}`
(p.15); every such `ℓ` is allowed. -/
theorem lemma_4_7 :
    ∀ K₀ : ℝ, 0 < K₀ → ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (Δ ℓ : ℕ) (Q : SimpleGraph V),
        1 ≤ ℓ → ℓ ^ 10 ≤ Δ → (∀ v, (Q.degree v : ℝ) ≤ K₀ * Δ) →
        ∀ U : Finset V, U.card ≤ Δ →
          (∀ Fs : Finset (Sym2 V),
              (∀ e ∈ Fs, ¬ e.IsDiag ∧ (∀ x ∈ e, x ∈ U) ∧ e ∉ Q.edgeSet) →
              (ℓ : ℝ) ≤ (Fs.card : ℝ) / Δ →
              1 - Real.exp (-(c * ((Fs.card : ℝ) / Δ))) ≤
                proposalProb Δ p fun ω =>
                  c * ((Fs.card : ℝ) / Δ) ≤
                    ((Finset.univ.filter fun col : Fin Δ =>
                      ∃ e ∈ Fs, ∀ x ∈ e, Retains Q ω x col).card : ℝ)) ∧
          (ℓ ≤ U.card →
              1 - Real.exp (-(c * (U.card : ℝ))) ≤
                proposalProb Δ p fun ω =>
                  c * (U.card : ℝ) ≤
                    ((Finset.univ.filter fun col : Fin Δ =>
                      ∃ x ∈ U, Retains Q ω x col).card : ℝ)) := by sorry

end DynBrooks
