-- Prove2me | Theorems.Thm_AESIndependence_Main_Supplement_spectral_gap_mixing
-- name    : AESIndependence.Main.Supplement.spectral_gap_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:03:05.53926+00:00
-- url     : https://prove2.me/theorems/78c689e5-1ae1-4897-97ec-4efa530dd63f
-- title:
--   Theorem 2.16 (companion theorem) — spectral-gap mixing and factor-six transfer
-- statement:
--   Let $n,t$ be natural numbers and let $\Omega_t$ be the finite set of ordered injective $t$-tuples of $n$-bit strings. Assume $|\Omega_t|\ge2$. Let $W$ be any real symmetric positive semidefinite stochastic transition matrix on this space, using $K(y,x)=\Pr[x\to y]$. Let $\lambda_2(W)$ be its second eigenvalue counted with multiplicity and $\gamma(W)=1-\lambda_2(W)>0$. Write $u(y)=1/|\Omega_t|$ and $d_{\mathrm{TV}}(\mu,u)=\frac12\sum_y|\mu(y)-u(y)|$.
--
--   There exists an absolute constant $C>0$, independent of every instance and accuracy parameter, with the following property. For every $0<\varepsilon<1$, set
--
--   $$
--   T=\left\lceil C\frac{nt+\ln(1/\varepsilon)}{\gamma(W)}\right\rceil.
--   $$
--
--   Both conclusions hold:
--
--   1. For every integer $r\ge T$ and starting tuple $x\in\Omega_t$,
--   $$d_{\mathrm{TV}}\big((W^r)(\cdot,x),u\big)\le\varepsilon.$$
--   2. For every doubly stochastic real matrix $P$ on the same space satisfying $W=(P^3)^{\mathsf T}P^3$, every integer $r\ge6T$ and every starting tuple $x$ satisfy
--   $$d_{\mathrm{TV}}\big((P^r)(\cdot,x),u\big)\le\varepsilon.$$
--
--   This companion theorem supplies the general conversion from a symmetric spectral gap to worst-case mixing, including a transfer to chains that need not be reversible. It retains both clauses of Theorem 2.16 in one item. The matrices are arbitrary; no AES parameter bounds or permutation-label realization are assumed.
--
--   **Formalization Note** The published tuple, uniform-mass, total-variation, and multiplicity-sensitive gap definitions are reused. Mathlib provides stochastic matrices and positive semidefiniteness. The witness $C$ is existential and absolute; the paper prints no numerical value. The quantitative explanation on p.5 permits, for example, $C=2$ in this ceiling convention; that derived example is not hard-coded in the statement. The factor six compares the displayed upper bounds, not the exact optimal mixing times.
--
--   Differences from the source:
--   - encoding: ordered t-tuples of distinct n-bit strings, with a defined second eigenvalue → DistinctTuple (Fin n → ZMod 2) t with cardinality at least two; reason: the same finite binary tuples, explicitly excluding only spaces where the second eigenvalue is undefined
--   - encoding: a symmetric positive semidefinite Markov operator W and a doubly stochastic P_M → real matrices with Mathlib colStochastic and PosSemidef for W, and doublyStochastic for P; reason: PosSemidef includes real symmetry; the existing column convention K(y,x)=Pr[x→y] is used for actual matrix powers
--   - encoding: τ_ε(W)=O((nt+log(1/ε))/γ(W)), with the same upper bound for P_M up to a factor of 6 → one absolute C>0 before n,t,W,ε,P and all starting states; T=ceil(C(nt+ln(1/ε))/spectralGap W); all r≥T mix W and all r≥6T mix P; reason: natural rounding and TV contraction express the mixing-time upper bounds without an empty-set infimum; log bases change only the universal witness, and 6 multiplies the same rounded bound
--   - encoding: λ₂(W), the second largest eigenvalue, and γ(W)=1−λ₂(W) → lambdaTwo W = 1 − spectralGap W, with spectralGap W the infimum of Σ_x f(x)(f(x)−(Wf)(x)) over mean-zero unit vectors f; reason: for a symmetric stochastic W on at least two states the constant vector is a top eigenvector and the mean-zero subspace is invariant, so this infimum is attained and equals 1−λ₂(W) (multiplicity-sensitive)
--   - encoding: W=(P_M^3)^T·P_M^3 with the paper's (unstated) transition-matrix orientation → W=(P^3)^T·P^3 for P in the column convention P(y,x)=Pr[x→y]; reason: if the paper's P_M is row-oriented this is W=P_M^3(P_M^3)^T instead, but for doubly stochastic A=P^3 both A^T A and A A^T preserve the mean-zero subspace and have the same spectrum there, so λ₂, γ and the bound T are the same under either orientation and each version implies the other
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 2.16, p.13 (PDF p.13); §2.3, p.12 (PDF p.12); quantitative explanation p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AESIndependence_Main_Supplement_MatrixMixing

namespace AESIndependence.Main.Supplement

/-- Theorem 2.16 (both clauses), Pelecanos–Tessaro–Vaikuntanathan,
STOC 2027 submission #1279, p.13 (PDF p.13); quantitative explanation p.5.
A single absolute positive constant gives a uniform mixing bound for every symmetric
positive semidefinite stochastic matrix on ordered distinct binary tuples, and six
times the same rounded bound for every doubly stochastic `P` with `W = (P³)ᵀ P³`.
`PosSemidef` includes symmetry over the reals; `colStochastic` fixes the column convention.
There is no AES parameter restriction or assumed convergence. The all-later-times encoding
avoids a natural infimum of an empty set of successful times. -/
theorem spectral_gap_mixing :
    ∃ C : ℝ, 0 < C ∧ ∀ (n t : ℕ),
      2 ≤ Fintype.card (DistinctTuple (Fin n → ZMod 2) t) →
      ∀ W : Matrix (DistinctTuple (Fin n → ZMod 2) t)
        (DistinctTuple (Fin n → ZMod 2) t) ℝ,
      W ∈ Matrix.colStochastic ℝ (DistinctTuple (Fin n → ZMod 2) t) →
      W.PosSemidef → lambdaTwo W < 1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      let T : ℕ := ⌈C * ((n : ℝ) * (t : ℝ) + Real.log (1 / ε)) /
        spectralGap W⌉₊
      (∀ r : ℕ, T ≤ r → MixedAt W ε r) ∧
      (∀ P : Matrix (DistinctTuple (Fin n → ZMod 2) t)
        (DistinctTuple (Fin n → ZMod 2) t) ℝ,
        P ∈ doublyStochastic ℝ (DistinctTuple (Fin n → ZMod 2) t) →
        W = (P ^ 3).transpose * P ^ 3 →
        ∀ r : ℕ, 6 * T ≤ r → MixedAt P ε r) := by sorry

end AESIndependence.Main.Supplement
