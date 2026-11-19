-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- name    : EnvyFreeCake104.Divide.ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-18T18:48:35.027277+00:00
-- url     : https://prove2.me/theorems/1252e13c-bedb-42e5-810e-8ec338bc87ec
-- title:
--   Containment and composition of suffixes of ordered pieces
-- statement:
--   A well-formed piece is its own suffix, every suffix lies inside it, suffixes of a retained suffix lift to the original piece, and original suffixes contained in the retained suffix remain suffixes of it. Prove this by comparing positions in the ordered interval list, handling empty intervals and out-of-range cuts explicitly.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

theorem EnvyFreeCake104.Divide.ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
    (Q : Piece) (hQ : Q.WF) :
    IsSuffix Q.toSet Q ∧
    (∀ S : Set ℝ, IsSuffix S Q → S ⊆ Q.toSet) ∧
    ∀ p : Pos, (prefixList Q p).WF → (suffixList Q p).WF →
      (∀ S : Set ℝ, IsSuffix S (suffixList Q p) → IsSuffix S Q) ∧
      (∀ S : Set ℝ, IsSuffix S Q → S ⊆ (suffixList Q p).toSet →
        IsSuffix S (suffixList Q p)) := by sorry
