-- Prove2me | Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
-- name    : DiazModulus.four_exponentials_trdeg_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T14:47:19.30305+00:00
-- url     : https://prove2.me/theorems/2c0f35ea-b824-4ce3-a701-01b48dc27a97
-- title:
--   Four exponentials in transcendence degree one (Brownawell; Waldschmidt)
-- statement:
--   The four exponentials conjecture is a **theorem** in transcendence degree one. This node states that case, unconditionally.
--
--   Let $\lambda_{11},\lambda_{12},\lambda_{21},\lambda_{22}$ be non-zero logarithms of algebraic numbers with
--
--   $$\lambda_{11}\lambda_{22}=\lambda_{12}\lambda_{21},\qquad \operatorname{trdeg}_{\mathbb Q}\mathbb Q(\lambda_{11},\lambda_{12},\lambda_{21},\lambda_{22})\le 1 .$$
--
--   Then the two rows, or the two columns, of $\begin{pmatrix}\lambda_{11}&\lambda_{12}\\ \lambda_{21}&\lambda_{22}\end{pmatrix}$ are linearly dependent over $\mathbb Q$.
--
--   **Attribution.** This is Theorem 1 of D. Roy and M. Waldschmidt, *Quadratic relations between logarithms of algebraic numbers*, Proc. Japan Acad. Ser. A **71** (1995), 151–153, where it is stated in the equivalent form: if $x_1,x_2$ are linearly independent over $\mathbb Q$, and $y_1,y_2$ likewise, and $\mathbb Q(x_1,x_2,y_1,y_2)$ has transcendence degree $1$ over $\mathbb Q$, then at least one of $e^{x_1y_1}, e^{x_1y_2}, e^{x_2y_1}, e^{x_2y_2}$ is transcendental. The two forms are identified in the paper itself, which states that its Theorem 1 "is the special case of Theorem 2 when $P$ is $X_1X_4-X_2X_3$ with $n=4$".
--
--   Roy and Waldschmidt do not claim the result as their own — the paper gives a new proof and refers for the original to **W. D. Brownawell**, *The algebraic independence of certain numbers related by the exponential function*, J. Number Theory **6** (1974), 22–31, Cor. 7, and to **M. Waldschmidt**, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), 191–202, Cor. 4. The paper opens by recording that the four exponentials conjecture "has been solved only in one special case, namely when the transcendence degree of the field which is spanned by the four logarithms is 1".
--
--   **Statement checked against the source.** The 1995 paper states the hypothesis as transcendence degree exactly $1$. This node writes $\le 1$: the degree-zero case is vacuous here, since four non-zero *algebraic* $\lambda_{ij}$ with $e^{\lambda_{ij}}$ algebraic contradict Hermite–Lindemann, available on this mission as the Proved node `DiazModulus.hermite_lindemann_holds`.
--
--   **Relation to `Diaz.four_exp_trdeg_one`.** That node states the same conclusion over an arbitrary subfield $K\subset\mathbb C$ and carries a master dichotomy as the explicit hypothesis `hMaster`, because Carlo Perassi's derivation of that dichotomy from Théorème 0.2 of D. Roy and M. Waldschmidt, *Approximation diophantienne et indépendance algébrique de logarithmes*, Ann. Sci. École Norm. Sup. (4) **30** (1997), 753–796, is not formalised. This node is the $K=\overline{\mathbb Q}$ case, first recorded on the authority of the 1995 paper above and since proved. Neither supersedes the other: the $K$-general form is not supported by this source.
--
--   **Formalization note.** Transcendence degree is `Algebra.trdeg ℚ` of `Algebra.adjoin ℚ` of the four numbers, and "linearly dependent over $\mathbb Q$" is the existence of a non-zero rational pair annihilating the two rows, respectively the two columns.
--
--   ---
--
--   **Formalisation status.** Proved. On 14 September 2026 this node was reduced to the nodes of the `FourExp` development, and all of them are now proved. The proof follows Waldschmidt's 1973 argument with the toolbox of his 1971 paper (Bull. Soc. Math. France **99** (1971), 285–304): Siegel's lemma, a Gel'fond-type transcendence criterion, the maximum principle, and a zero count for exponential polynomials that needs no separation hypothesis. That zero count is what lets the argument drop hypotheses (iii) and (iv) of Lemme 2 of the 1973 paper, the second of which the paper meets with Gel'fond's lower bound for linear forms in two logarithms (pp. 195 and 199). Philippon's zero estimate is not needed. A scoping pass of 8 September 2026 had concluded the opposite and called this node a citation boundary; that assessment was wrong about the route and is withdrawn.
--
--   The six exponentials **theorem** does not imply this statement: six exponentials is a $3\times2$ result, this is $2\times2$ together with a transcendence-degree hypothesis, and no deduction of the second from the first is known.
-- source:
--   D. Roy and M. Waldschmidt, "Quadratic relations between logarithms of algebraic numbers", Proc. Japan Acad. Ser. A 71 (1995), 151-153, Theorem 1. Author's copy: https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/ProjectEuclid/ProcJapanAcad71-1995.pdf (publication list: https://webusers.imj-prg.fr/~michel.waldschmidt/texts.html). Attributed there to W. D. Brownawell, J. Number Theory 6 (1974), 22-31, Cor. 7, and M. Waldschmidt, J. Number Theory 5 (1973), 191-202, Cor. 4.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem four_exponentials_trdeg_one :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
      ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by sorry
end DiazModulus
