-- Prove2me | Theorems.Thm_DerivativeChainContinuation_full_compression_deficit_theorem
-- name    : DerivativeChainContinuation.full_compression_deficit_theorem
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:05:42.987251+00:00
-- url     : https://prove2.me/theorems/953ea8af-095e-47d3-b5bf-877548e8503e
-- title:
--   Actual compression and the complete C3–C4 deficit package
-- statement:
--   Let $p$ be centered and monic of degree $m\ge2$. There is an $m\times m$ complex matrix $B$ with $$\chi_B=X\operatorname{monicDerivative}(p),\quad\|B\|_F^2=(m-2)V(p),\quad\|[B,B^*]\|_F^2=8\det\Sigma(p).$$ Moreover $$\delta(p)=\|B\|_F^2-\sum_{\chi_B(\lambda)=0}|\lambda|^2\ge0,\qquad\frac{\det\Sigma(p)}{2R(p)^2}\le\delta(p).$$ All spectra count multiplicity. The ambient compression has the additional zero eigenvalue.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitComplete.lean#L16-L40

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.full_compression_deficit_theorem (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), n=p.natDegree ∧
      B.charpoly = X*monicDerivative p ∧
      frobeniusSq B = ((p.natDegree : ℝ)-2)*rootVariance p ∧
      frobeniusSq (B*B.conjTranspose-B.conjTranspose*B) = 8*(rootCovariance p).det ∧
      schoenbergDeficit p = frobeniusSq B-(B.charpoly.roots.map Complex.normSq).sum ∧
      0 ≤ schoenbergDeficit p ∧
      (rootCovariance p).det/(2*(rootRadius p)^2) ≤ schoenbergDeficit p := by sorry
