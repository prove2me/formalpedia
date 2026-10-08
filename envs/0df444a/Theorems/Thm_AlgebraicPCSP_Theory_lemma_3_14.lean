-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_lemma_3_14
-- name    : AlgebraicPCSP.Theory.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:31.301987+00:00
-- url     : https://prove2.me/theorems/0dacd6f4-9bc2-4174-bdb4-c420383890f0
-- title:
--   Lemma 3.14 — I → A makes Σ(A, I) trivial; Pol(A, B) satisfying Σ(A, I) gives I → B
-- statement:
--   Let $\mathbf A$, $\mathbf B$ and $\mathbf I$ be similar finite relational structures (finite signature, arities $\ge1$, nonempty finite domains), and let $\Sigma=\Sigma(\mathbf A,\mathbf I)$ be the bipartite minor condition built from a fixed enumeration $A=\{a_1,\dots,a_n\}$ and fixed enumerations of the relations $R^{\mathbf A}$ (§3.2). Then:
--
--   1. if there is a homomorphism $h:\mathbf I\to\mathbf A$, then $\Sigma$ is trivial;
--   2. if $\mathrm{Pol}(\mathbf A,\mathbf B)$ satisfies $\Sigma$, then there is a homomorphism $\mathbf I\to\mathbf B$.
--
--   In symbols,
--   $$\big(\mathbf I\to\mathbf A\ \Rightarrow\ \Sigma(\mathbf A,\mathbf I)\text{ trivial}\big)\quad\text{and}\quad\big(\mathrm{Pol}(\mathbf A,\mathbf B)\models\Sigma(\mathbf A,\mathbf I)\ \Rightarrow\ \mathbf I\to\mathbf B\big).$$
--
--   These are the completeness and soundness of the reduction from $\mathrm{PCSP}(\mathbf A,\mathbf B)$ to promise satisfaction of minor conditions. Part 2 is the step (3) ⇒ (4) of Theorem 4.12.
--
--   **Formalization Note** Triviality is satisfaction in the projection minion on a two-element set. Part 2 uses satisfaction in the family of all polymorphisms of positive arity, which needs no template hypothesis, as in the paper.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 20, Lemma 3.14 (construction of Σ(A, I): p. 19, §3.2)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Lemma 3.14 (arXiv:1811.00970v3, p. 20). Let `𝔸`, `𝔹` and `𝕀` be similar finite structures,
and let `Σ = Σ(𝔸, 𝕀)` be built from the enumeration `e` of `A` and the enumerations `eR R` of
the relations `R^𝔸` (§3.2, p. 19). Then
(1) if there is a homomorphism `h : 𝕀 → 𝔸`, then `Σ` is trivial; and
(2) if `Pol(𝔸, 𝔹)` satisfies `Σ`, then there is a homomorphism from `𝕀` to `𝔹`. -/
theorem lemma_3_14 {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B I : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (𝕀 : RelStruct τ ar I)
    {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ) (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) :
    ((∃ h : I → A, IsHom 𝕀 𝔸 h) → IsTrivial (sigmaCondition 𝔸 𝕀 e m eR)) ∧
    (SatisfiedIn (sigmaCondition 𝔸 𝕀 e m eR) (polFamily 𝔸 𝔹) → ∃ h : I → B, IsHom 𝕀 𝔹 h) := by sorry

end AlgebraicPCSP.Theory
