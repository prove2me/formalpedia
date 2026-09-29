-- Prove2me | Theorems.Thm_ColemanMandula_lemma7_trace_is_linear
-- name    : ColemanMandula.lemma7_trace_is_linear
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T05:01:40.63586+00:00
-- url     : https://prove2.me/theorems/ece15dd0-ec05-4442-a4e6-634070103193
-- title:
--   Coleman–Mandula Lemma 7: $\operatorname{Tr}B(p)$ is linear in $p$
-- statement:
--   Assume particle finiteness, weak elastic analyticity and occurrence of scattering, and let $B\in\mathfrak B_S$. Then on every hyperboloid $H_k$ the trace of $B$ is an affine function of the four-momentum: there exist a four-vector $a$ and $c\in\mathbb R$ such that
--   $$\operatorname{Tr}B_k(p)=a\cdot p+c\qquad\text{for all }p\in H_k .$$
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1256, Lemma 7 (Eq. (29))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma7_trace_is_linear (D : ScatteringData)
    (hfin : D.ParticleFinite) (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs)
    (B : D.Multiplier) (hB : D.IsSymMultiplier B) (k : D.Shell) :
    ∃ (a : FourVec) (c : ℝ), ∀ p ∈ massShell (D.mass k),
      (B k p).trace = ((mdot a p + c : ℝ) : ℂ) := by
  sorry

end ColemanMandula
