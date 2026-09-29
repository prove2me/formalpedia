-- Prove2me | Theorems.Thm_BraidsLinksMCG_artinBraidGroup_equiv_artinTits_generatorMatched
-- name    : BraidsLinksMCG.artinBraidGroup_equiv_artinTits_generatorMatched
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T05:59:22.831572+00:00
-- url     : https://prove2.me/theorems/27bb4c27-27c4-44f8-9627-22c3d2f125ae
-- title:
--   Generator-matched form of the Artin–Tits identification
-- statement:
--   The platform's hand-written presentation `ArtinBraidGroup n` is isomorphic to the Artin–Tits group of type $A_{n-1}$ **by an isomorphism carrying each generator to the corresponding generator**: there is a multiplicative equivalence $e$ with
--
--   $$e(\sigma_i) = \text{of}(i) \qquad \text{for every } i.$$
--
--   The existing theorem `BraidsLinksMCG.artinBraidGroup_equiv_artinTits` already establishes that the two groups are abstractly isomorphic, asserting `Nonempty (ArtinBraidGroup n ≃* artinTitsA n)`. That form is not sufficient for transporting statements about the generators, because an abstract isomorphism carries no information about where the generators go: only properties invariant under isomorphism can be moved across it.
--
--   This statement supplies the missing data. The relator sets of the two presentations coincide generator-for-generator — for type $A$ the Coxeter entries are $m_{ii'}=3$ for adjacent indices and $m_{ii'}=2$ otherwise, giving exactly the braid relation and the commutation relation of the hand-written set — so the identity map on generators is expected to induce the isomorphism. Making that explicit is what allows results proved for the standard Artin–Tits model to be applied to generator-level statements about `ArtinBraidGroup`, such as the half-twist results of this mission.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.15 (injectivity half); combined with the Artin–Tits identification recorded in `BraidsLinksMCG.artinBraidGroup_equiv_artinTits` (Proved). Cf. Birman, Braids, Links and Mapping Class Groups, Ch. 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinTitsA

open CoxeterSystem

namespace BraidsLinksMCG

theorem artinBraidGroup_equiv_artinTits_generatorMatched (n : ℕ) :
    ∃ e : ArtinBraidGroup n ≃* artinTitsA n,
      ∀ i : Fin (n - 1), e (sigma i) = PresentedGroup.of i := by sorry

end BraidsLinksMCG
