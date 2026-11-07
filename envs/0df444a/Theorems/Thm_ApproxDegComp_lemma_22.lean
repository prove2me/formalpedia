-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_22
-- name    : ApproxDegComp.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:01.921739+00:00
-- url     : https://prove2.me/theorems/c86c40cb-3f8b-46c5-bce3-a73b2e969f52
-- title:
--   Lemma 22 — $R=\mathbb E_{\rho_\theta}Q$ is a $[0,1]$-valued trigonometric polynomial of total frequency $\le\deg Q$, and $\mathcal S(R)(z/\kappa)=\mathbb E_{\nu}Q$
-- statement:
--   Let $\mathcal X\subseteq\{0,1\}^m$, let $E_0,\dots,E_m$ be real orthogonal projectors on $\mathbb R^{\mathcal X}$ with $\sum_kE_k=I$ satisfying the banded property (9) of Lemma 20, let $d\in\mathbb N$ and $A=\sum_k\min\{k,d\}E_k$, let $v\in\mathbb C^{\mathcal X}$ be a unit vector, $\rho_\theta(x)=|(e^{i\theta A}v)_x|^2$, let $\kappa\ne0$ and $\nu_b=\rho_0+\frac{z}{\kappa}\rho_0'$ for $b=(1+z)/2$, $z\in\{-1,1\}$. Let $Q$ be a real multilinear polynomial on $n$ blocks of $m$ bits of degree at most $D$ with $0\le Q\le1$ on $\{0,1\}^{mn}$, and
--
--   $$R(\theta_1,\dots,\theta_n)=\mathbb E_{X^{(i)}\sim\rho_{\theta_i}}\bigl[Q(X^{(1)},\dots,X^{(n)})\bigr].$$
--
--   Then
--
--   1. $R$ is a real-valued trigonometric polynomial with total frequency at most $D$;
--   2. $0\le R\le1$ on $\mathbb R^n$;
--   3. for every $z\in\{-1,1\}^n$,
--   $$\mathcal S(R)(z/\kappa)=\mathbb E_{X^{(i)}\sim\nu_{(1+z_i)/2}}\,Q(X^{(1)},\dots,X^{(n)}).\tag{11}$$
--
--   The banded structure converts the degree of $Q$ into the total frequency of $R$; this is the step that transfers degree of an approximant of $f\circ g$ into a frequency bound.
--
--   Differences from the source:
--   - generalization: ρ_θ "as described in the previous Lemma 21" (with X, E, A of Lemma 20, v = (u₀+iu₁)/√2, κ = 2λ, ν₀, ν₁ of Lemma 21) → any projectors E summing to I with property (9), A = Σ min{k,d}E_k, any unit vector v ∈ ℂ^X, any κ ≠ 0 and ν given by ν_b = ρ₀ + (z/κ)ρ′₀; reason: Lemma 20/21's objects satisfy these hypotheses (v is a unit vector, κ = 2λ > 0, and the ν of Lemma 21 satisfy its "Consequently" clause), so the statement specializes to the source's
--   - encoding: ρ_θ on X → ρ_θ on {0,1}^m, equal to 0 outside X; reason: the expectation only sees X
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 22, p.22 (proof Appendix B, pp.48–49)

import Mathlib
import Definitions.Def_ApproxDegComp_IsMultilinear
import Definitions.Def_ApproxDegComp_sqfreeFun
import Definitions.Def_ApproxDegComp_HasTotalFreqLE
import Definitions.Def_ApproxDegComp_zOf
import Definitions.Def_ApproxDegComp_blockExpect
import Definitions.Def_ApproxDegComp_mulOp
import Definitions.Def_ApproxDegComp_levelMat
import Definitions.Def_ApproxDegComp_rho

namespace ApproxDegComp

/-- **Lemma 22**, p.22 (proof in Appendix B, pp.48–49).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 22, p.22: "Let Q be a real multilinear polynomial on n disjoint blocks of m bits each.
Let degree of Q be at most D and 0 ≤ Q ≤ 1 on the Boolean cube {0, 1}^{mn}. Let X⁽¹⁾, …, X⁽ⁿ⁾ be
n independent disjoint blocks such that X⁽ⁱ⁾ is sampled from ρ_{θᵢ}, where θᵢ ∈ ℝ and ρ_{θᵢ} are
as described in the previous Lemma 21. Let R be defined as follows: R(θ₁, …, θₙ) =
E_{X⁽ⁱ⁾∼ρ_{θᵢ}}[Q(X⁽¹⁾, …, X⁽ⁿ⁾)]. Then, R is a real-valued trigonometric polynomial with total
frequency at most D and 0 ≤ R ≤ 1 on ℝⁿ. Furthermore, the squarefree extraction of R satisfies:
S(R)(z/κ) = E_{X⁽ⁱ⁾∼ν_{(1+zᵢ)/2}} Q(X⁽¹⁾, …, X⁽ⁿ⁾) (z ∈ {−1, 1}ⁿ). (11)"

**Formalization Note** "ρ_θ as described in Lemma 21" is spelled out as hypotheses: orthogonal
projectors `E_0, …, E_m` on `ℝ^X` summing to `I` with the banded property (9) of Lemma 20,
`A = levelMat E d = Σ_k min{k, d} E_k`, a unit vector `v ∈ ℂ^X`, `ρ_θ = rho X A v θ`, a scalar
`κ ≠ 0` and `ν_b = ρ₀ + (zOf b/κ) ρ′₀` (the relation (11) is about). Lemma 21's `v`, `κ = 2λ`
and `ν` satisfy these. `Q` is evaluated at the 0/1 points; coordinate `(i, j)` is bit `j` of
block `i`. -/
theorem lemma_22 (n m D d : ℕ) (X : Finset (Fin m → Bool)) (E : Fin (m + 1) → Matrix X X ℝ)
    (hE : ∀ k, (E k).transpose = E k ∧ E k * E k = E k) (hEsum : ∑ k, E k = 1)
    (hband : ∀ (r : ℕ) (p : MvPolynomial (Fin m) ℝ), p.totalDegree ≤ r →
      ∀ k l : Fin (m + 1), (r : ℤ) < |(k : ℤ) - (l : ℤ)| → E k * mpoly X p * E l = 0)
    (v : X → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) (κ : ℝ) (hκ : κ ≠ 0)
    (ν : Bool → (Fin m → Bool) → ℝ)
    (hν : ∀ b x, ν b x = rho X (levelMat E d) v 0 x +
      zOf b / κ * deriv (fun θ => rho X (levelMat E d) v θ x) 0)
    (Q : MvPolynomial (Fin n × Fin m) ℝ) (hQ : IsMultilinear Q) (hQD : Q.totalDegree ≤ D)
    (hQ01 : ∀ x, 0 ≤ MvPolynomial.eval (cubePt x) Q ∧ MvPolynomial.eval (cubePt x) Q ≤ 1)
    (R : (Fin n → ℝ) → ℝ)
    (hR : ∀ θ, R θ = blockExpect (fun i => rho X (levelMat E d) v (θ i))
      (fun x => MvPolynomial.eval (cubePt x) Q)) :
    HasTotalFreqLE (fun θ => (R θ : ℂ)) D ∧ (∀ θ, 0 ≤ R θ ∧ R θ ≤ 1) ∧
      ∀ z : Fin n → Bool, sqfreeFun R (fun i => zOf (z i) / κ) =
        blockExpect (fun i => ν (z i)) (fun x => MvPolynomial.eval (cubePt x) Q) := by sorry

end ApproxDegComp
