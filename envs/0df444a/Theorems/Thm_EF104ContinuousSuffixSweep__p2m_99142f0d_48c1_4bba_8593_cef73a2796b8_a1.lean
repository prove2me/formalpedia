-- Prove2me | Theorems.Thm_EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- name    : EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T15:23:13.831185+00:00
-- url     : https://prove2.me/theorems/fb070949-5cbe-4304-85c1-778db8a5a5e4
-- title:
--   Continuous nested suffix sweep for a well-formed ordered piece
-- statement:
--   Every well-formed ordered piece has a nested sweep through suffixes from empty to whole, continuously and monotonically valued by every nonnegative integrable density. Prove this by induction on its interval list, using continuity of moving interval integrals. Empty and degenerate intervals are allowed.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Model
open EnvyFreeCake104.Divide

theorem EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
    (Q : Piece) (hQ : Q.WF) :
    ∃ S : ℝ → Set ℝ,
      S 0 = ∅ ∧ S 1 = Q.toSet ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsSuffix (S t) Q) ∧
      MonotoneOn S (Set.Icc (0 : ℝ) 1) ∧
      ∀ v : Valuation,
        ContinuousOn (fun t ↦ v.value (S t)) (Set.Icc (0 : ℝ) 1) ∧
        MonotoneOn (fun t ↦ v.value (S t)) (Set.Icc (0 : ℝ) 1) := by
  sorry
