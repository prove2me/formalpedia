-- Prove2me | Theorems.Thm_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
-- name    : AutomorphicForm.unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6cab5960-fe98-5745-8499-5a1bf98ae1c9
-- title:
--   Unipotent fibre of a GL₂ Cartan double coset and its measure bound
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, and $K_v$ the $v$-adic completion with valuation subring $\mathcal{O}_v$. Let $\varpi \in \mathcal{O}_v$ be irreducible, let $m_2 \le m_1$ be integers, let $dl \in \mathrm{GL}_2(K_v)$ have underlying matrix $\mathrm{diag}(\varpi^{m_1}, \varpi^{m_2})$, let $a \neq b$ in $K_v$ and let $t \in \mathrm{GL}_2(K_v)$ have underlying matrix $\mathrm{diag}(a,b)$; fix the Borel measurable structure on $K_v$ and an additive Haar measure $\nu$. Write $n(u)$ for the unit of $M_2(K_v)$ with matrix $\begin{pmatrix}1&u\\0&1\end{pmatrix}$, and let $\mathcal{K}$ be the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in $\mathcal{O}_v$. Then: (i) $\|\varpi\| = (\mathrm{absNorm}\, v)^{-1}$; (ii) for every $u \in K_v$, $n(u)^{-1} t\, n(u) \in \mathcal{K}\, dl\, \mathcal{K}$ if and only if $\|ab\| = \|\varpi\|^{m_1+m_2}$ and $\max(\|a\|, \|b\|, \|(a-b)u\|) = \|\varpi\|^{m_2}$; (iii) for every $n \in \mathbb{Z}$, $\|a-b\| \cdot \nu\{u : \|(a-b)u\| \le \|\varpi\|^n\} = \|\varpi\|^n \nu(\mathcal{O}_v)$; (iv) likewise with equality $\|(a-b)u\| = \|\varpi\|^n$ in place of the inequality, the value being $\|\varpi\|^n (1 - \|\varpi\|) \nu(\mathcal{O}_v)$; and (v) $\|a-b\| \cdot \nu\{u : n(u)^{-1} t\, n(u) \in \mathcal{K}\, dl\, \mathcal{K}\} \le \|\varpi\|^{m_2} \nu(\mathcal{O}_v)$. All measures are the real-valued ones.
--
--   This computes the support along the unipotent fibre of the indicator of the Hecke double coset attached to $\mathrm{diag}(\varpi^{m_1}, \varpi^{m_2})$ at a split regular diagonal element, evaluates the measure of the relevant balls and spheres, and deduces the Macdonald-type bound on the resulting local orbital integral. It is used in the uniform bound for the measures of the sets of upper-triangular elements lying in such a double coset.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ m₁, (ϖ : v.adicCompletion K) ^ m₂])
    (a b : v.adicCompletion K) (hab : a ≠ b) (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, b])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ∧
    (∀ u : v.adicCompletion K,
      (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v ↔
        ‖a * b‖ = ‖(ϖ : v.adicCompletion K)‖ ^ (m₁ + m₂) ∧
          max (max ‖a‖ ‖b‖) ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ m₂) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    (∀ n : ℤ, ‖a - b‖ * ν.real {u : v.adicCompletion K | ‖(a - b) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * (1 - ‖(ϖ : v.adicCompletion K)‖) *
        ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    ‖a - b‖ * ν.real {u : v.adicCompletion K |
        (AutomorphicForm.unipotentGL2 u)⁻¹ * t * AutomorphicForm.unipotentGL2 u ∈
          AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v} ≤
      ‖(ϖ : v.adicCompletion K)‖ ^ m₂ * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by sorry
