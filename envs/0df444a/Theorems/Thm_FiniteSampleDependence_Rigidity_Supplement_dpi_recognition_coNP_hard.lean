-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_dpi_recognition_coNP_hard
-- name    : FiniteSampleDependence.Rigidity.Supplement.dpi_recognition_coNP_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:53:44.068622+00:00
-- url     : https://prove2.me/theorems/867f1ccc-7dd2-4241-b990-88773d66586d
-- title:
--   Theorem D.1 — recognizing (LF-DPI) for circuit-represented rational polynomials is coNP-hard, already on $F_A=(\det U)^2c(U)^\top Ac(U)$
-- statement:
--   Consider the decision problem: given $n\ge2$ (part of the input) and an arithmetic circuit over $\mathbb Q$ computing a polynomial $F$ in the entries $U_{i\alpha}$ of an $n\times n$ matrix, decide whether $F$ satisfies (LF-DPI), i.e.
--   $$F(TU)\le F(U)\qquad\text{for every }U\in\Delta_{n,n}\text{ and every column-stochastic }T\in\mathbb R^{n\times n}.$$
--   Let $\mathrm{DPIRec}$ be the language of binary codes of the yes-instances. Then:
--
--   1. $\mathrm{DPIRec}$ is coNP-hard: every coNP language over every finite nonempty alphabet reduces to it by a polynomial-time many-one reduction;
--   2. the hardness holds for the family
--   $$F_A(U)=(\det U)^2\,c(U)^\top A\,c(U),\qquad A\in\mathbb Q^{n\times n},\ A=A^\top:$$
--   for every coNP language $L'$ there is such a reduction $f$ every output of which is the code of a well-formed circuit, with some $n\ge2$, computing $F_A$ for some symmetric rational $A$;
--   3. every polynomial in this family is row-permutation invariant, $F_A(QU)=F_A(U)$ for every permutation matrix $Q$ and every real $U$, and independence-zero on $\Delta_{n,n}$.
--
--   Here $c(U)=U^\top\mathbf 1_n$ is the column marginal. The result shows that the class of polynomial DPI monotones, whose square-determinant factor is forced by the mission's goal, has no polynomial-time membership test unless P = NP.
--
--   Differences from the source:
--   - encoding: a rational polynomial represented by an arithmetic circuit, n part of the input → a pair (n, C) with C a list of gates (variables U_{iα}, rational constants, +, −, ×) in topological order, the last gate being the output; reason: the paper fixes no circuit format; this is the standard straight-line-program model with its gate set
--   - encoding: the decision problem 'does F satisfy (LF-DPI)' → the language DPIRec ⊆ {0,1}* of codes (n, C) with n ≥ 2, C well formed, and the computed polynomial satisfying (LF-DPI) on Δ_{n,n}; other strings are outside; reason: an explicit prefix-free binary encoding (self-delimiting naturals, reduced rationals) fixes the problem as a language; decoding is unique and polynomial time
--   - encoding: coNP-hard → every coNP language over every finite nonempty alphabet poly-time many-one reduces to DPIRec (published CookPvsNP framework); reason: the standard definition of coNP-hardness under Karp reductions
--   - encoding: 'the hardness holds for the family F_A' → the reduction's every output is the code of a well-formed circuit computing F_A for some rational symmetric A; reason: this is the hardness of DPIRec restricted to codes of the family
--   - encoding: F is a rational polynomial and (LF-DPI) is tested over real U and T → the circuit's polynomial with coefficients cast from ℚ to ℝ, evaluated on real matrices; reason: the condition in the theorem quantifies over real U ∈ Δ_{n,n} and real T
--   - reading: 'every polynomial in this family is row-permutation invariant' → F_A(QU) = F_A(U) for every permutation matrix Q and every real n×n matrix U; reason: invariance of a polynomial read as an identity on all matrices, the stronger of the readings (the simplex-only reading follows)
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem D.1, PDF p. 27 (printed p. 26), Appendix D

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Circuits

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Theorem D.1 (DPI recognition is coNP-hard), PDF p. 27 (printed p. 26). With `n ≥ 2` part of
the input, deciding whether a rational polynomial given by an arithmetic circuit satisfies
(LF-DPI) on `Δ_{n,n}` is coNP-hard. The hardness holds for the family
`F_A(U) = (det U)² c(U)ᵀ A c(U)` (`A ∈ ℚ^{n×n}`, `A = Aᵀ`): every coNP language reduces in
polynomial time to `DPIRec` by a reduction whose every output is the code of a circuit computing
some `F_A`. Every `F_A` is row-permutation invariant and independence-zero. -/
theorem dpi_recognition_coNP_hard :
    CoNPHard DPIRec ∧
    (∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
      L' ∈ CookPvsNP.coNP Sym' →
        ∃ f : List Sym' → List Bool, CookPvsNP.PolyTimeComputable f ∧
          (∀ x, x ∈ L' ↔ f x ∈ DPIRec) ∧
          ∀ x, ∃ (n : ℕ) (C : Circuit) (A : Matrix (Fin n) (Fin n) ℚ),
            2 ≤ n ∧ C.WellFormed n ∧ Aᵀ = A ∧ C.poly n = faPoly n A ∧
              f x = encodeInstance n C) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℚ, Aᵀ = A →
      (∀ (σ : Equiv.Perm (Fin n)) (U : Matrix (Fin n) (Fin n) ℝ),
          faFun A (σ.permMatrix ℝ * U) = faFun A U) ∧
        IZ (faFun A)) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
