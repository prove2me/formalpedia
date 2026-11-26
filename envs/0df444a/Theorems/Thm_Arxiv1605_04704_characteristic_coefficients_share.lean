-- Prove2me | Theorems.Thm_Arxiv1605_04704_characteristic_coefficients_share
-- name    : Arxiv1605_04704.characteristic_coefficients_share
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T20:06:27.510154+00:00
-- url     : https://prove2.me/theorems/452d5f9e-1a7c-41cc-939d-9f5e8a695f78
-- title:
--   Section 3, eq. (19) paragraph: the coefficients of the characteristic decomposition collect equal shares of the spectral weights
-- statement:
--   Let $M$ be a real $4\times4$ matrix with $m_{00}>0$ satisfying the covariance criterion, and let $H(M)=m_{00}U\operatorname{diag}(\hat\lambda_0,\dots,\hat\lambda_3)U^\dagger$ with $U$ unitary and $\hat\lambda_0\ge\hat\lambda_1\ge\hat\lambda_2\ge\hat\lambda_3$. Then the coefficients of the characteristic decomposition (15) satisfy
--
--   $$1-P_3=4\hat\lambda_3,\qquad P_3-P_2=3(\hat\lambda_2-\hat\lambda_3),\qquad P_2-P_1=2(\hat\lambda_1-\hat\lambda_2).$$
--
--   Each coefficient collects an equal share from the spectral components:
--
--   1. $(1-P_3)M_{\Delta0}=\hat\lambda_3\,(M_{U0}+M_{U1}+M_{U2}+M_{U3})$;
--   2. $(P_3-P_2)M_3=(\hat\lambda_2-\hat\lambda_3)(M_{U0}+M_{U1}+M_{U2})$;
--   3. $(P_2-P_1)M_2=(\hat\lambda_1-\hat\lambda_2)(M_{U0}+M_{U1})$.
--
--   This is the redistribution of spectral weights that the paper uses for the filtering of Section 5.
--
--   **Formalization Note** The paper's phrase "a contribution of amount $\hat\lambda_3$ from each of the four pure components" (and likewise for $M_3$, $M_2$) is stated as the identities 1-3 between Mueller matrices.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c003; Section 3, paragraph after eq. (19), with eqs. (10), (11), (14), (15), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem characteristic_coefficients_share (M : Matrix (Fin 4) (Fin 4) ℝ) (hm : 0 < M 0 0)
    (hpsd : (cohMat M).PosSemidef) (U : Matrix.unitaryGroup (Fin 4) ℂ) (l : Fin 4 → ℝ)
    (hs : IsSpectralData M U l) :
    1 - ipp3 l = 4 * l 3 ∧ ipp3 l - ipp2 l = 3 * (l 2 - l 3) ∧ ipp2 l - ipp1 l = 2 * (l 1 - l 2) ∧
    (1 - ipp3 l) • idealDepol (M 0 0) =
      l 3 • (specComp U (M 0 0) 0 + specComp U (M 0 0) 1 + specComp U (M 0 0) 2 +
        specComp U (M 0 0) 3) ∧
    (ipp3 l - ipp2 l) • depol3 U (M 0 0) =
      (l 2 - l 3) • (specComp U (M 0 0) 0 + specComp U (M 0 0) 1 + specComp U (M 0 0) 2) ∧
    (ipp2 l - ipp1 l) • depol2 U (M 0 0) =
      (l 1 - l 2) • (specComp U (M 0 0) 0 + specComp U (M 0 0) 1) := by sorry

end Arxiv1605_04704
