-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_isotopy_maps_hopf
-- name    : BirkhoffGlobalSection.contact_isotopy_maps_hopf
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T04:38:41.624802+00:00
-- url     : https://prove2.me/theorems/bceaf620-cae0-4f28-9485-a80cb72366c2
-- title:
--   A sphere contact isotopy carries the standard Hopf circle through transverse embeddings
-- statement:
--   Let $F_t$ be a smooth antipodally equivariant, coorientation-preserving contact isotopy of the standard three-sphere, starting at the identity and ending at $F$. Write $H(u)=(u_1,0,-u_2,0)$ for the positive standard Hopf circle. Then its image under the endpoint map belongs to the equivariant transverse Hopf isotopy class:
--
--   $$F(H(S^1))\text{ admits an equivariant positive transverse isotopy from }H(S^1).$$
--
--   The conclusion includes joint smoothness, sphere membership, embeddedness and positive contact evaluation at every time, together with the exact final image. This supplies the passage from an ambient contact isotopy to an isotopy of the chosen binding.
-- source:
--   Direct chain-rule consequence of the definitions in Def_BirkhoffGlobalSection_SphereContact and Def_BirkhoffGlobalSection_TransverseHopf: alpha_H(u)(DH(u)Ju)=1/2 and F_t^*alpha=a_t alpha, a_t>0. Contact-isotopy convention: Min, arXiv:2207.03590v2, Section 1.1, p. 2, https://arxiv.org/pdf/2207.03590.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem contact_isotopy_maps_hopf (F : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (F.toFun '' (standardHopfCircle '' unitCircle))) := by sorry

end BirkhoffGlobalSection
