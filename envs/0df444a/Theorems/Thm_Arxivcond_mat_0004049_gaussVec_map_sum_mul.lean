-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_gaussVec_map_sum_mul
-- name    : Arxivcond_mat_0004049.gaussVec_map_sum_mul
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T15:11:19.522204+00:00
-- url     : https://prove2.me/theorems/c86efade-6789-421c-80d7-a588b3d0aad3
-- title:
--   A unit-vector projection of the Gaussian column is a circular complex Gaussian with variance $1/N$
-- statement:
--   Let $N \ge 1$ and let $v = (v_1, \dots, v_N)$ be the complex Gaussian vector of the model: independent circular complex Gaussian entries with $\mathbb{E}|v_i|^2 = 1/N$, i.e. real and imaginary parts independent $N(0, 1/(2N))$. Let $u \in \mathbb{C}^N$ be a fixed unit vector, $\sum_i |u_i|^2 = 1$. Then
--
--   $$
--   \sum_{i=1}^N u_i v_i
--   $$
--
--   is again a circular complex Gaussian with $\mathbb{E}\left|\sum_i u_i v_i\right|^2 = 1/N$: its real and imaginary parts are independent $N(0, 1/(2N))$.
--
--   In the paper this is the step behind Rayleigh's law for $n \ne m$: conditionally on the incident column $u$, the reflected amplitude $A_0 = \sum_i u_i v_i$ is Gaussian with variance $\sum_i |u_i|^2 / N = 1/N$, independently of $u$.
--
--   **Formalization Note** The vector $v$ has law `gaussVec N` from the mission definitions file, and the target law is the image of `(gaussianReal 0 (1/(2N))).prod (gaussianReal 0 (1/(2N)))` under $(x, y) \mapsto x + iy$.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 2, the paragraph before eq. (11) ("independent Gaussian random numbers with vanishing mean and variance $N^{-1}$") and eq. (1)

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

theorem gaussVec_map_sum_mul (N : ℕ) (u : Fin N → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1) :
    (gaussVec N).map (fun v => ∑ i, u i * v i) =
      ((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map
        Complex.measurableEquivRealProd.symm := by sorry

end Arxivcond_mat_0004049
