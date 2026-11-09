-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_information_complexity_matrix_multiplication
-- name    : CaiZhuInfo.Matrix.information_complexity_matrix_multiplication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:46.629192+00:00
-- url     : https://prove2.me/theorems/290ccb16-e983-4ed4-9e77-488f61f018f3
-- title:
--   Theorem 1.2 — Information complexity of matrix multiplication
-- statement:
--   Let $F$ be any finite field of size $q$, let $m\ge1$ and $1\le t\le s$, and use independent uniform inputs $X\in F^{t\times m}$ and $Y\in F^{s\times m}$. For every real $0\le\varepsilon\le1$, put $\alpha=\max(1-q^{ts}\varepsilon/(q^{ts}-1),0)$ and $\kappa=\mathbb E_{\Lambda\ne0}[t/\operatorname{rank}\Lambda]$, with $\Lambda$ uniform among all nonzero tests. Then
--   $$[\alpha mt\log_2q-c_0\kappa]^+\le\mathrm{IC}^{B,\mathrm{av}}_U(\mathrm{MM}_{t,s,m},\varepsilon)\le\mathrm{IC}^{B,\mathrm{pw}}_U(\mathrm{MM}_{t,s,m},\varepsilon)\le\alpha mt\log_2q.$$
--   The same lower bound holds for transcript-determined output under both error conventions. At zero error, both Bob-only complexities equal
--   $$\mathrm{IC}^B_U(\mathrm{MM}_{t,s,m},0)=mt\log_2q.$$
--   The displayed upper bound minus the displayed positive-part lower bound is at most $2c_0<9.544$ bits, uniformly over all parameters, where $c_0=\log_2(16+8\sqrt2)<4.772$. This is the complete source theorem, including exact equality and the universal gap.
--
--   Differences from the source:
--   - encoding: finite randomized protocols with public and private randomness → finite binary trees with independent measurable tape probability spaces and derived execution laws; reason: finite messages admit binary coding and arbitrary real mixture probabilities are retained; no common round bound is imposed
--   - encoding: F_q, matrix dimensions, and the two error/output conventions → an arbitrary finite field of cardinality q, Fin-indexed matrices, and four separately constrained actual protocol infima; reason: all finite-field instances, all real errors in [0,1], both zero-error conventions and the exact constants are preserved
--   - encoding: information cost I(X;Π | Y) + I(Y;Π | X), with Π containing the public tape and every message → I(H;X | Y,R) + I(H;Y | X,R), where H is the finite complete-history label and R is the public tape; reason: independence of the public tape from the inputs, the chain rule and symmetry of conditional mutual information give the same cost; the finite first slot also covers infinite discrete input alphabets
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Theorem 1.2, (6)–(7) and universal gap sentence, printed p.3 / PDF p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_matrixProduct

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem information_complexity_matrix_multiplication
    {F : Type} [Field F] [Fintype F]
    (m t s : ℕ) (hm : 0 < m) (ht : 0 < t) (hts : t ≤ s)
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    let upper := alpha F t s ε * (m : ℝ) * t * logTwo (Fintype.card F)
    let lower := max (upper - c₀ * kappa F t s) 0
    (lower ≤ matrixIC F t s m ε false false) ∧
    (matrixIC F t s m ε false false ≤ matrixIC F t s m ε true false) ∧
    (matrixIC F t s m ε true false ≤ upper) ∧
    (lower ≤ matrixIC F t s m ε false true) ∧
    (lower ≤ matrixIC F t s m ε true true) ∧
    (matrixIC F t s m 0 false false = (m : ℝ) * t * logTwo (Fintype.card F)) ∧
    (matrixIC F t s m 0 true false = (m : ℝ) * t * logTwo (Fintype.card F)) ∧
    (upper - lower ≤ 2 * c₀) ∧ (c₀ < 4.772) ∧ (2 * c₀ < 9.544) := by sorry

end CaiZhuInfo.Matrix
