-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_7_7
-- name    : ArbSlowFP.proposition_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:10.845101+00:00
-- url     : https://prove2.me/theorems/61ad2c86-ed72-4693-bf6e-4532565429c3
-- title:
--   Proposition 7.7 — every proposed run is valid
-- statement:
--   For the fixed parameters of Section 7.2 there is an integer threshold $Q_{\mathrm{out}}$ such that for every integer $q\ge Q_{\mathrm{out}}$, the best-response updates starting from $u(q)=\mathrm{col}(s(q),v(q))$ follow the exact word $A(q)B(q)$ and end at $u(q+1)$. During the parent bundle no added action interrupts the parent. Action $g$ plays once at the bundle endpoint, followed by exactly $m_j(q)$ consecutive plays of each reset action $a_j$ in increasing order of $j$. Throughout this reset block, including its entry and endpoint, the maximum score among all actions equals $\zeta(q)$.
--
--   **Formalization Note** The word is `outerWord`, whose structure gives the clauses on the order of plays. Validity is under the priority $(63)$. The run lengths in the word are natural numbers, and the statement asserts that they equal the values $m_j(q)$.
--
--   Differences from the source:
--   - generalization: T₂ fixed by Proposition 7.6 → every admissible T₂ with T₁ ≥ T₀; reason: the proof uses only the bounds of Lemma 7.5, which are uniform in T₂; the fixed T₂ is one of these
--   - encoding: the fixed section R and threshold Q_out → Q_out after T₁, T₂, and T₀ after R; reason: p.49 fixes R first; Q_out belongs to one fixed game
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), quantified before T₀; reason: every linear map on im L extends to the whole space and every such map restricts to one; Rmap is only evaluated on im L at the T₁ ≥ T₀ the statement covers
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.58, Proposition 7.7

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Proposition 7.7, p.58 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For parameters
as in §7.2 there is an integer threshold `Q_out` such that for every integer `q ≥ Q_out` the best-response
updates from `u(q) = col(s(q), v(q))` follow the exact word `A(q)B(q)` and end at `u(q+1)`: the parent bundle
without interruption by an added action, then `g` once, then exactly `m_j(q)` plays of each reset action
`a_j` in increasing order of `j`. Throughout the reset block, including its entry and endpoint, the maximum
score among all actions equals `ζ(q)`.

**Formalization Note.** The word `outerWord` is `A(q)B(q)`, with its structure by definition; validity is
under the priority (63). The statement holds for every admissible `T₂`, since the section's estimates
are uniform in `T₂`; the paper's fixed `T₂` is one of these. -/
theorem proposition_7_7 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hR : IsSection Rmap) :
    let L := d.liftParams τ cref ℓs aP Rmap
    ∃ T0 : ℕ, 1 ≤ T0 ∧ ∀ T1 T2 : ℕ, T0 ≤ T1 → L.IsAdmissible T1 T2 →
      ∃ Qout : ℕ, 1 ≤ Qout ∧ L.IsOuterThreshold d.rank d.W T1 T2 Qout := by sorry

end ArbSlowFP
