-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_e_system_specialization_data
-- name    : EulerMascheroni.Mixed.e_system_specialization_data
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:52:53.795794+00:00
-- url     : https://prove2.me/theorems/7ebb2cc0-c1f4-4916-bbd9-b1f8ffc4544a
-- title:
--   Differential system and canonical values at one for the Euler E-functions
-- statement:
--   For $f=(1,e^X,e^X\operatorname{Ein}(X))$, prove the formal system
--   $$Xf'=\begin{pmatrix}0&0&0\\0&X&0\\-1&1&X\end{pmatrix}f.$$
--   The canonical power-series values at $1$ are $(1,e,e\operatorname{Ein}(1))$. The denominator polynomial is $X$, which does not vanish at $1$. This supplies the differential equations and evaluation identifications for classical specialization.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, pp. 1–6, especially Corollary 2.2 and Theorem 3.2. Explicit specialization and arithmetic verification for the Euler system.

import Definitions.Def_rationalEArithmetic
import Definitions.Def_eulerMascheroni_formalESystem
open ArithmeticE PowerSeries EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.e_system_specialization_data :
    (∀ i : Fin 3,
    (PowerSeries.X:PowerSeries ℂ)*PowerSeries.derivative ℂ
      (![1,PowerSeries.exp ℂ,formalExpEin] i) =
    ∑ j : Fin 3, (((!![0,0,0;0,Polynomial.X,0;-1,1,Polynomial.X] : Matrix (Fin 3) (Fin 3) (Polynomial ℚ)) i j).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (![1,PowerSeries.exp ℂ,formalExpEin] j)) ∧
    (∀ i : Fin 3,
    seriesValue (![1,PowerSeries.exp ℂ,formalExpEin] i) 1 =
      (![1,Complex.exp 1,expEin 1] i)) := by sorry
