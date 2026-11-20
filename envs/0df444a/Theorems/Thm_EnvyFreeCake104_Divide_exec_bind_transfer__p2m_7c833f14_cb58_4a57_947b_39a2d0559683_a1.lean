-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- name    : EnvyFreeCake104.Divide.exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T06:58:00.49742+00:00
-- url     : https://prove2.me/theorems/58b54c2a-60fe-4158-b73e-8c0bf7b0cdaf
-- title:
--   Successful protocol prefixes transfer continuations through a shifted oracle
-- statement:
--   After any successful protocol prefix, a shifted choice oracle makes each successful continuation lift to the composed protocol under the original oracle, with exactly additive query counts.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (a : Proto ι α) (b : α → Proto ι β) (s : Rec ι)
    (x : α) (s₁ : Rec ι) (tr₁ : List (Event ι))
    (ha : exec V o a s = some (x, s₁, tr₁)) :
    ∃ o₁ : ChoiceOracle ι, ∀ (y : β) (s₂ : Rec ι) (tr₂ : List (Event ι)),
      exec V o₁ (b x) s₁ = some (y, s₂, tr₂) →
      ∃ tr : List (Event ι),
        exec V o (do let z ← a; b z) s = some (y, s₂, tr) ∧
        queryCount tr = queryCount tr₁ + queryCount tr₂ := by sorry
