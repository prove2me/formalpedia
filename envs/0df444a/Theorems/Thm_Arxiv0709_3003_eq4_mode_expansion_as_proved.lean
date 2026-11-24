-- Prove2me | Theorems.Thm_Arxiv0709_3003_eq4_mode_expansion_as_proved
-- name    : Arxiv0709_3003.eq4_mode_expansion_as_proved
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:21:24.198723+00:00
-- url     : https://prove2.me/theorems/1f8cd0be-fd9d-4305-a0b5-6600edac5944
-- title:
--   Eq. (4) (as proved): Gaussian expansion of the mean squared correlation
-- statement:
--   Let $N\ge0$, $s>0$ and $|\rho|\le s$. Let $u_1,\dots,u_N$ be random vectors on a probability space with $u_n=(u_n(S_i),u_n(S_j),u_n(R))$, each a centred Gaussian vector with covariance
--
--   $$\begin{pmatrix}s&\rho&0\\\rho&s&0\\0&0&s\end{pmatrix},$$
--
--   and let distinct modes be uncorrelated: $E[u_n(a)u_m(b)]=0$ for $n\ne m$ and all coordinates $a,b$. Then
--
--   $$\Big\langle\sum_{n=1}^N u_n(S_i)^2u_n(S_j)^2u_n(R)^4\Big\rangle=3N\,s^2\big(s^2+2\rho^2\big).$$
--
--   **Formalization Note** The paper prints $\langle C_{ij}^2\rangle=\langle u^2\rangle^2(\langle u^2\rangle^2+2\langle u_n(S_i)u_n(S_j)\rangle^2)$, Eq. (4). Its proof, the Gaussian expansion of Eq. (3) with the receiver uncorrelated with the sources, gives the factor $E[u_n(R)^4]=3s^2$ and the factor $N$ from the sum over modes. Both constants are absent from the printed formula. They cancel in the normalised ratio of Eq. (2). The statement is the value the expansion gives. The hypothesis that distinct modes are uncorrelated is the paper's and is not needed for the identity.
-- source:
--   Larose, Lobkis and Weaver, Coherent backscattering of ultrasound without a source, arXiv:0709.3003v1 (2007), claim c013; first experiment, Eqs. (3)-(4), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv0709_3003_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv0709_3003

theorem eq4_mode_expansion_as_proved {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (N : ℕ) (s ρ : ℝ) (hs : 0 < s) (hρ : |ρ| ≤ s)
    (u : Fin N → Omega → EuclideanSpace ℝ (Fin 3)) (hu : ∀ n, HasLaw (u n) (modeLaw s ρ) P)
    (hunc : ∀ n m : Fin N, n ≠ m → ∀ a b : Fin 3, ∫ ω, u n ω a * u m ω b ∂P = 0) :
    ∫ ω, (∑ n, u n ω 0 ^ 2 * u n ω 1 ^ 2 * u n ω 2 ^ 4) ∂P =
      N * (3 * s ^ 2 * (s ^ 2 + 2 * ρ ^ 2)) := by sorry

end Arxiv0709_3003
