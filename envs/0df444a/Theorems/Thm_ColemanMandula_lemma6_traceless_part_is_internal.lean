-- Prove2me | Theorems.Thm_ColemanMandula_lemma6_traceless_part_is_internal
-- name    : ColemanMandula.lemma6_traceless_part_is_internal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T04:56:40.679704+00:00
-- url     : https://prove2.me/theorems/bfad372d-dd97-4517-991c-eabacc3b4779
-- title:
--   Coleman–Mandula Lemma 6: $B^*$ is an infinitesimal internal symmetry
-- statement:
--   Assume particle finiteness, weak elastic analyticity and occurrence of scattering, and let $B\in\mathfrak B_S$. Then on every hyperboloid $H_k$ the traceless part $b(p)=B_k(p)^*$ is an infinitesimal internal symmetry transformation: $b(p)$ is Hermitian and
--   $$b(\Lambda p)\,W_k(\Lambda,p)=W_k(\Lambda,p)\,b(p)\qquad\text{for all }p\in H_k\text{ and all proper orthochronous Lorentz }\Lambda,$$
--   i.e. the multiplication operator $b$ commutes with the unitary action of the Lorentz group (and hence with the whole Poincaré group). In Wigner's standard spin bases this says that $b$ is independent of $p$ and commutes with rotations.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, pp. 1255–1256, Lemma 6

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma6_traceless_part_is_internal (D : ScatteringData)
    (hfin : D.ParticleFinite) (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs)
    (B : D.Multiplier) (hB : D.IsSymMultiplier B) (k : D.Shell) :
    D.IsInternalOn k (fun p => ScatteringData.tracelessPart (B k p)) := by
  sorry

end ColemanMandula
