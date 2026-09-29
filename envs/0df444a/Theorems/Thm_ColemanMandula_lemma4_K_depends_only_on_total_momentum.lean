-- Prove2me | Theorems.Thm_ColemanMandula_lemma4_K_depends_only_on_total_momentum
-- name    : ColemanMandula.lemma4_K_depends_only_on_total_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T04:41:10.384576+00:00
-- url     : https://prove2.me/theorems/54b34e8e-b2b3-41e7-8329-1acc4590e2b1
-- title:
--   Coleman–Mandula Lemma 4: $K(p,q)$ depends only on $p+q$
-- statement:
--   Let $D$ satisfy weak elastic analyticity and occurrence of scattering. Let $(p,q)$ be a good pair on hyperboloids $(H_k,H_l)$ and let $p'\in H_k$, $q'\in H_l$ with $p+q=p'+q'$. Then
--   $$K(p,q)=K(p',q'),$$
--   where $K(p,q)=\{B\in\mathfrak B_S : B^*(p,q)=0\}$ is the set of symmetric multipliers whose two-particle action $B(p)\otimes1+1\otimes B(q)$ is a multiple of the identity at $(p,q)$.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1255, Lemma 4 (Eqs. (18)–(22))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma4_K_depends_only_on_total_momentum (D : ScatteringData)
    (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs) (k l : D.Shell)
    (p q p' q' : FourVec) (hpq : D.GoodPair k l p q)
    (hp' : p' ∈ massShell (D.mass k)) (hq' : q' ∈ massShell (D.mass l))
    (hsum : p + q = p' + q') :
    D.Kset k l p q = D.Kset k l p' q' := by
  sorry

end ColemanMandula
