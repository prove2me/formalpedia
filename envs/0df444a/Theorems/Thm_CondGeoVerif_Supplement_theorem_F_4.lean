-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_F_4
-- name    : CondGeoVerif.Supplement.theorem_F_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:18:20.26821+00:00
-- url     : https://prove2.me/theorems/829b0d6f-ea9b-4d2a-9331-0e02a331d9c3
-- title:
--   Theorem F.4 — every slab width has a low-noise regime with an $O_t(\varepsilon^{-1}\log(e/(\varepsilon\delta)))$ proper one-message verifier
-- statement:
--   Fix a slab width $t>0$, centered slabs $S_{t,d}=\{x\mapsto2\cdot1\{|w\cdot x|\le t\}-1:w\in S^{d-1}\}$ and features $X\sim N(0,I_d)$. There is $\eta_t>0$ such that every $0\le\eta\le\eta_t$ admits a one-message proper slab verifier with full Massart completeness at noise bound $\eta$ and arbitrary-label soundness using
--   $$m_V=O_t\Big(\varepsilon^{-1}\log\frac e{\varepsilon\delta}\Big),\qquad m_P=O_t\Big(\frac{d\log(e/\varepsilon)+\log(e/(\varepsilon\delta))}{\varepsilon^2}\Big),$$
--   for every $d\ge1$, $0<\varepsilon<1$ and $0<\delta\le1/4$. The constants and $\eta_t$ depend only on $t$.
--
--   Differences from the source:
--   - encoding: O_t(·), η_t → η_t and one constant C chosen after t, before η, d, ε, δ; reason: the subscript names the only dependence
--   - encoding: ranges of d, ε, δ (not restated in the theorem) → d ≥ 1, 0 < ε < 1, 0 < δ ≤ 1/4; reason: the paper's standing ranges (§2, p.3); S^{d−1} is nonempty for d ≥ 1
--   - reading: there is η_t > 0 (a Massart noise bound) → 0 < η_t < 1/2; reason: Massart bounds lie in [0, 1/2); the proof takes η_t ≤ 1/4
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem F.4, p.48 (PDF p.51); proof pp.48–49

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem F.4** (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, p.48 = PDF p.51). For each fixed slab width `t > 0` there is
`η_t > 0` such that every `0 ≤ η ≤ η_t` admits a one-message proper verifier for centered slabs
`S_{t,d}` with full Massart completeness and arbitrary-label soundness using
`m_V = O_t(ε⁻¹ log(e/(εδ)))` private samples and an honest prover with
`m_P = O_t((d log(e/ε) + log(e/(εδ)))/ε²)` samples.

**Formalization Note** The `O_t` constant `C` and `η_t` depend only on `t`: they are chosen before
`η, d, ε, δ`. `d ≥ 1` (so `S^{d−1}` is nonempty), `0 < ε < 1`, `0 < δ ≤ 1/4` (the paper's standing
ranges). `η_t < 1/2` is the standing range of Massart noise. -/
theorem theorem_F_4 (t : ℝ) (ht : 0 < t) :
    ∃ ηt : ℝ, 0 < ηt ∧ ηt < 1 / 2 ∧ ∃ C : ℝ, ∀ η : ℝ, 0 ≤ η → η ≤ ηt →
      ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
          ProperIn V ({slabRule t} : Set (Vec 1 → Bool)) ∧
          OMSound V (slabClass t d) ε δ ∧
          OMMassartComplete V Hon (slabClass t d) η ε δ ∧
          (V.m : ℝ) ≤ C * (1 / ε) * Real.log (Real.exp 1 / (ε * δ)) ∧
          (Hon.mP : ℝ) ≤ C * ((d * Real.log (Real.exp 1 / ε) +
            Real.log (Real.exp 1 / (ε * δ))) / ε ^ 2) := by sorry

end CondGeoVerif.Supplement
