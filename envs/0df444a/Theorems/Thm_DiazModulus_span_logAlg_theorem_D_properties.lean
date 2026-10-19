-- Prove2me | Theorems.Thm_DiazModulus_span_logAlg_theorem_D_properties
-- name    : DiazModulus.span_logAlg_theorem_D_properties
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T17:48:00.978235+00:00
-- url     : https://prove2.me/theorems/3c674580-9a0c-42dd-b958-1221cd425017
-- title:
--   ℒ itself has all the Theorem D properties, and Diaz's conjecture holds exactly when no non-zero element of ℒ has algebraic modulus
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic), and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Let $L = \mathrm{span}_{\mathbb{Q}}(\mathcal{L})$ and $\widetilde L = \mathrm{span}_{\overline{\mathbb{Q}}}(\{1\} \cup L)$. Then Diaz's conjecture (`DiazModulus.DiazModulusConjecture`: $e^u$ is transcendental for every $u \neq 0$ with $|u|$ algebraic) holds if and only if no $u \in L$ with $u \neq 0$ has $|u|$ algebraic, and $L$ has the following properties:
--
--   - **(conjugation)** $\bar z \in L$ for every $z \in L$;
--   - **(Baker)** if $n \geq 0$, $l_1, \dots, l_n \in L$ are linearly independent over $\mathbb{Q}$, and $b_0, b_1, \dots, b_n$ are algebraic numbers, not all zero, then $b_0 + \sum_{i=1}^{n} b_il_i \neq 0$;
--   - **(Hermite–Lindemann)** every algebraic $z \in L$ is $0$;
--   - **(Gel'fond–Schneider)** if $l_0 \neq 0$ and $\beta l_0$ both lie in $L$ and $\beta$ is algebraic, then $\beta \in \mathbb{Q}$;
--   - **(Roy, relative to $\widetilde{\mathcal{L}}$)** if no $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, have all six products $x_iy_j$ in $\widetilde{\mathcal{L}}$, then no such families have all six products in $\widetilde L$;
--   - **(six exponentials)** no $x_1, x_2 \in \mathbb{C}$, linearly independent over $\mathbb{Q}$, and $y_1, y_2, y_3 \in \mathbb{C}$, linearly independent over $\mathbb{Q}$, have all six products $x_iy_j$ in $L$;
--   - **(four exponentials in transcendence degree one)** if $\ell_{11}, \ell_{12}, \ell_{21}, \ell_{22} \in L$ are non-zero, $\ell_{11}\ell_{22} = \ell_{12}\ell_{21}$, and the $\mathbb{Q}$-algebra they generate has transcendence degree at most $1$ over $\mathbb{Q}$, then there are $a, b \in \mathbb{Q}$, not both zero, with $a\ell_{11} + b\ell_{21} = a\ell_{12} + b\ell_{22} = 0$ (the rows of the matrix $(\ell_{ij})$ are linearly dependent over $\mathbb{Q}$), or with $a\ell_{11} + b\ell_{12} = a\ell_{21} + b\ell_{22} = 0$ (its columns are).
--
--   Since $\mathcal{L}$ is a $\mathbb{Q}$-vector space, $L = \mathcal{L}$ and $\widetilde L = \widetilde{\mathcal{L}}$. The Roy clause is an implication: Roy's strong six exponentials theorem for $\widetilde{\mathcal{L}}$ (Roy 1992, Cor. 2) is its hypothesis, not a hypothesis of the node, so the statement is unconditional.
--
--   **What it means.** `DiazModulus.span_logAlg_theorem_D_properties` shows that $\mathcal{L}$ itself has these properties and that Diaz's conjecture says exactly that no non-zero element of $\mathcal{L}$ has algebraic modulus, while `DiazModulus.theorem_D_barrier` gives a $\mathbb{Q}$-space $L' \supseteq \mathcal{L}$ with the same properties that does contain such an element. So the listed properties, as axioms about $(\mathcal{L}, \widetilde{\mathcal{L}})$ (with Roy's theorem for $\widetilde{\mathcal{L}}$ supplying the hypothesis of the Roy clause), do not prove Diaz's conjecture: an argument from them alone would apply to $L'$ and its $\overline{\mathbb{Q}}$-span with $1$ as well. Here a candidate for $L'$ means a non-zero $u \in L'$ with $|u|$ algebraic; it is not `DiazModulus.IsCandidate`, which asks for $e^u$ to be algebraic. The barrier is a model-existence statement about membership only: the model has no exponential function, so it says nothing about arguments through the values $e^{x_iy_j}$, such as Waldschmidt's theorem of 1973, or through Roy's rank bounds for larger matrices.
--
--   **Proof.** The $\mathbb{Q}$-span of $\mathcal{L}$ is $\mathcal{L}$, by `DiazModulus.mem_logAlg_adjoin_circle_point_iff` at $u = 0$, so membership in $L$ means $e^z$ algebraic, and Diaz's conjecture is the contrapositive of the statement that no non-zero $u \in L$ has $|u|$ algebraic. The clauses are then the classical theorems read off their nodes: conjugation is `DiazModulus.logAlg_conj_stable`, Baker is `Schanuel.baker_linear_forms_in_logarithms`, Hermite–Lindemann is `DiazModulus.hermite_lindemann_holds`, Gel'fond–Schneider is `Schanuel.gelfond_schneider` (a non-rational $\beta$ would make $e^{\beta l_0}$ transcendental), six exponentials is `DiazModulus.six_exponentials`, and four exponentials is `DiazModulus.four_exponentials_trdeg_one`, verbatim. The Roy clause holds because $\widetilde L$ is contained in $\widetilde{\mathcal{L}}$.
--
--   **Novelty.** Not found in the sources read as a bundle; routine. The clauses are classical theorems about $\mathcal{L}$: Baker (1966), Hermite–Lindemann, Gel'fond–Schneider (1934), the six exponentials theorem (Lang 1966, Ramachandra 1968) and the four exponentials theorem in transcendence degree one (Waldschmidt 1973, Brownawell 1974); the Roy clause is relative, so Roy's theorem (1992, Cor. 2) is not needed.
-- source:
--   Not found in the sources read as a bundle. The clauses are Baker's theorem (A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216); Hermite–Lindemann (Ch. Hermite 1873; F. Lindemann 1882); Gel'fond–Schneider (A. O. Gel'fond 1934; Th. Schneider 1934); the six exponentials theorem (S. Lang, Introduction to Transcendental Numbers, Addison-Wesley, 1966, chapter II; K. Ramachandra, Contributions to the theory of transcendental numbers I, II, Acta Arith. 14 (1968)); the four exponentials theorem in transcendence degree one (M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202; W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31); the Roy clause is an implication from Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2). Uses DiazModulus.mem_logAlg_adjoin_circle_point_iff, Schanuel.baker_linear_forms_in_logarithms, DiazModulus.hermite_lindemann_holds, Schanuel.gelfond_schneider, DiazModulus.six_exponentials, DiazModulus.four_exponentials_trdeg_one and DiazModulus.logAlg_conj_stable. R19 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem span_logAlg_theorem_D_properties :
    (DiazModulusConjecture ↔
      ∀ u ∈ Submodule.span ℚ LogAlg, u ≠ 0 → ¬ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) ∧
    /- conjugation -/
    (∀ z ∈ Submodule.span ℚ LogAlg, conj z ∈ Submodule.span ℚ LogAlg) ∧
    /- (D2) Baker -/
    (∀ (n : ℕ) (l : Fin n → ℂ), (∀ i, l i ∈ Submodule.span ℚ LogAlg) → LinearIndependent ℚ l →
      ∀ (b₀ : ℂ) (b : Fin n → ℂ), IsAlgebraic ℚ b₀ → (∀ i, IsAlgebraic ℚ (b i)) →
        (b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) → b₀ + ∑ i, b i * l i ≠ 0) ∧
    /- (D2) Hermite-Lindemann -/
    (∀ z ∈ Submodule.span ℚ LogAlg, IsAlgebraic ℚ z → z = 0) ∧
    /- (D2) Gel'fond-Schneider -/
    (∀ l₀ β : ℂ, l₀ ∈ Submodule.span ℚ LogAlg → β * l₀ ∈ Submodule.span ℚ LogAlg → l₀ ≠ 0 → IsAlgebraic ℚ β →
      ∃ q : ℚ, β = (q : ℂ)) ∧
    /- (D3) Roy, relative to ℒ: strong six exponentials for ℒ̃ gives it for span Q̄ (insert 1 L) -/
    ((∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) →
      ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
        LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
        ¬ (∀ i j, x i * y j ∈ Submodule.span Qbar (insert 1 ((Submodule.span ℚ LogAlg : Submodule ℚ ℂ) : Set ℂ)))) ∧
    /- (D3) six exponentials -/
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
      ¬ (∀ i j, x i * y j ∈ Submodule.span ℚ LogAlg)) ∧
    /- (D4) four exponentials in transcendence degree one -/
    (∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ, l₁₁ ∈ Submodule.span ℚ LogAlg → l₁₂ ∈ Submodule.span ℚ LogAlg → l₂₁ ∈ Submodule.span ℚ LogAlg → l₂₂ ∈ Submodule.span ℚ LogAlg →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 → l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) ∨
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0)) := by
  sorry

end DiazModulus
