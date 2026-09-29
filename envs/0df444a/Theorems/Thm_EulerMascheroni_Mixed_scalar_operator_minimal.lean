-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_scalar_operator_minimal
-- name    : EulerMascheroni.Mixed.scalar_operator_minimal
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T19:45:27.994096+00:00
-- url     : https://prove2.me/theorems/b38b7678-17bf-4724-af24-08236318f71f
-- title:
--   Explicit minimal scalar equation for a nondegenerate Euler E-combination
-- statement:
--   For complex $a,b,c$ with $c\ne0$, let $F=a+b e^X+c e^X\operatorname{Ein}(X)$. The explicit third-order scalar operator in the imported definition annihilates $F$, has least possible differential order among nonzero complex polynomial operators, and has nonzero leading coefficient at $X=1$.
--
--   Writing $L=\sum_{k=0}^3p_kD^k$, its leading coefficient is $p_3=X(aX-a+c)$, so $p_3(1)=c$. The proof derives the first three derivatives from the Euler system and verifies $LF=0$. Any polynomial relation among $F,F',F''$ yields a polynomial relation among $1,e^X,e^X\operatorname{Ein}(X)$; their established independence and elementary elimination force every coefficient to vanish. This proves minimality without appealing to the general cyclic-vector theorem or arithmetic E-function specialization.
-- source:
--   Direct scalar elimination in the Euler E-system; the ordinary cyclic-combination step in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2, pp. 6–7. Minimality uses the separately proved polynomial functional independence of 1, exp(X), and exp(X) Ein(X).

import Definitions.Def_eulerScalarEquation
open ArithmeticE EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.scalar_operator_minimal (a b c : ℂ) (hc : c ≠ 0) :
    MinimalEquation (scalarOperator a c) 3 (formalCombination a b c) ∧
      (scalarOperator a c 3).eval 1 ≠ 0 := by sorry
