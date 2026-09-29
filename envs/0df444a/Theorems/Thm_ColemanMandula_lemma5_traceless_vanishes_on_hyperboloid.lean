-- Prove2me | Theorems.Thm_ColemanMandula_lemma5_traceless_vanishes_on_hyperboloid
-- name    : ColemanMandula.lemma5_traceless_vanishes_on_hyperboloid
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T04:42:49.56648+00:00
-- url     : https://prove2.me/theorems/b84be99b-eb65-4b89-a62a-a31d492db9e7
-- title:
--   Coleman–Mandula Lemma 5: vanishing of $B^*$ propagates over the hyperboloid
-- statement:
--   Assume particle finiteness, weak elastic analyticity and occurrence of scattering. Let $(p,q)$ be a good pair with both momenta on the same hyperboloid $H_k$, and let $B\in\mathfrak B_S$ satisfy $B^*(p,q)=0$, i.e. $B_k(p)\otimes1+1\otimes B_k(q)$ is a multiple of the identity. Then
--   $$B_k(p')^*=B_k(p')-\tfrac{\operatorname{tr}B_k(p')}{N_k}\,1=0\qquad\text{for every }p'\in H_k .$$
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1255, Lemma 5 (Eqs. (23)–(28))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma5_traceless_vanishes_on_hyperboloid (D : ScatteringData)
    (hfin : D.ParticleFinite) (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs)
    (k : D.Shell) (p q : FourVec) (hpq : D.GoodPair k k p q)
    (B : D.Multiplier) (hB : D.IsSymMultiplier B)
    (h0 : ScatteringData.tracelessPart (ScatteringData.twoPart (B k p) (B k q)) = 0) :
    ∀ p' ∈ massShell (D.mass k), ScatteringData.tracelessPart (B k p') = 0 := by
  sorry

end ColemanMandula
