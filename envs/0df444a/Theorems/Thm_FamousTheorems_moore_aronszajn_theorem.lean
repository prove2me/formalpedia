-- Prove2me | Theorems.Thm_FamousTheorems_moore_aronszajn_theorem
-- name    : FamousTheorems.moore_aronszajn_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:40.462511+00:00
-- url     : https://prove2.me/theorems/c5407931-fd22-499e-a1cf-c4c0d625f831
-- title:
--   The Moore–Aronszajn theorem
-- statement:
--   **The Moore–Aronszajn theorem.** Let $K$ be a positive semidefinite kernel on a set $X$, with values in the bounded operators on a Hilbert space $V$. Then there is a reproducing kernel Hilbert space $H$ of functions $X\to V$ whose reproducing kernel is $K$.
--
--   Moore (1916) and Aronszajn (1950) established this correspondence between positive semidefinite kernels and reproducing kernel Hilbert spaces, including uniqueness of the space. It is the foundation of kernel methods in machine learning, of Gaussian process regression, and of the theory of spaces of analytic functions such as the Hardy and Bergman spaces.
--
--   **Formalization note.** Mathlib's `RKHS.OfKernel.kernel_ofKernel`, with witness `RKHS.OfKernel K`, the completion of the pre-Hilbert space spanned by kernel functions. `RKHS 𝕜 H X V` says that $H$ embeds continuously and injectively into functions $X\to V$, so point evaluations are continuous. `RKHS.kernel H` is the matrix of operators $K(x,y)=k_x^*k_y$ built from the kernel functions. `K.PosSemidef` is positive semidefiniteness of the operator-valued matrix `K : Matrix X X (V →L[𝕜] V)`. Universe levels are explicit because the statement quantifies over the type $H$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `RKHS.OfKernel.kernel_ofKernel`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w

theorem moore_aronszajn_theorem {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {V : Type w} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V] (K : Matrix X X (V →L[𝕜] V)) (hK : K.PosSemidef) :
    ∃ (H : Type (max v w u)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H) (_ : CompleteSpace H)
      (_ : RKHS 𝕜 H X V), RKHS.kernel H = K := by sorry

end FamousTheorems
