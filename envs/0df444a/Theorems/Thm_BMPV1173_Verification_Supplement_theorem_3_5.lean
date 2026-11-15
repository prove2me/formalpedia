-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_3_5
-- name    : BMPV1173.Verification.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:54:36.534201+00:00
-- url     : https://prove2.me/theorems/d707bcbe-a296-46f9-ab30-940e0c9e8b57
-- title:
--   Theorem 3.5 — Exact OV comparison, converse bound and BMPV lower bound
-- statement:
--   Let $Q(\mathrm{OV}_n)$ and $Q(\mathrm{BMPV}_n)$ be the published least worst-case query complexities for the single-list orthogonality and arbitrary Boolean verification problems. The theorem gives all three conclusions:
--
--   $$Q(\mathrm{OV}_n)\le Q(\mathrm{BMPV}_n)\quad(n\ge2),$$
--   $$Q(\mathrm{BMPV}_n)=O\bigl(Q(\mathrm{OV}_{2n+2})\bigr),\qquad Q(\mathrm{BMPV}_n)=\Omega(n^{5/4}).$$
--
--   The first inequality is pointwise for every $n\ge2$. The second has a fixed constant overhead and the exact dimension $2n+2$, with no additive term and no logarithmic loss. The final lower bound is the conclusion continuing onto p.20. Together these record the full verification/OV comparison.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
--   - encoding: Q(BMPV_n)=O(Q(OV_(2n+2))) → a fixed positive natural multiplier K with eventual ENat inequality qBMPV n <= K*qOV (2*n+2); reason: a positive real overhead can be rounded upward to an integer; extended-natural comparisons do not send infinity to zero
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 3.5, printed p.19-20 = PDF p.19-20.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics

namespace BMPV1173.Verification.Supplement

/-- Theorem 3.5 spans printed/PDF pp.19–20; the last clause is on p.20. -/
theorem theorem_3_5 :
    (∀ n : ℕ, 2 ≤ n → qOV n ≤ qBMPV n) ∧
    (∃ K N : ℕ, 0 < K ∧ ∀ n : ℕ, max 2 N ≤ n →
      qBMPV n ≤ (K : ENat) * qOV (2 * n + 2)) ∧
    OrdinaryDecisionLower VerificationIndex (fun _ => Set.univ) (fun _ => bmpv)
      (powerRate (5 / 4 : ℝ)) 2 := by sorry

end BMPV1173.Verification.Supplement
