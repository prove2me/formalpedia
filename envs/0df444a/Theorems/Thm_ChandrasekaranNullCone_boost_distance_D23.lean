-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_boost_distance_D23
-- name    : ChandrasekaranNullCone.boost_distance_D23
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T14:53:58.403145+00:00
-- url     : https://prove2.me/theorems/a959aef0-400b-44e4-8ede-656243af8599
-- title:
--   Boost distance bound for the doubled corner state, eq. (D.23)
-- statement:
--   Let $H=\mathbb{C}^n$ with its standard inner product, and let $\bar H$ be its conjugate copy, identified with $\mathbb{C}^n$ by complex conjugation of coordinates. Let $C\in M_n(\mathbb{C})$ be arbitrary (it plays the role of the weighted half-diamond preparation $C_b$), let $\hat s\in M_n(\mathbb{C})$ be Hermitian (the area operator $\hat s$, in units of $4G_N\hbar$), and let $\hat s^{*}=\overline{\hat s}$ be its entrywise complex conjugate (the area on the conjugate copy of the corner $S$). Let $(v_i)_{i\in I}$ be a finite orthonormal family in $H$, with time reflections $v_i^{*}=\overline{v_i}\in\bar H$, and let $P=\sum_i v_iv_i^{\dagger}$ be the orthogonal projection onto its span. Set $Z=\operatorname{Tr}(PC^{\dagger}C)\ge 0$,
--   $$\rho_P=\frac{PC^{\dagger}CP}{Z},\qquad |\Psi_P\rangle=\frac{1}{\sqrt{Z}}\sum_{i} C v_i\otimes v_i^{*}\in H\otimes\bar H .$$
--   Then for all real $s_0$ and $\eta$,
--   $$\Big\|\Big(\hat 1\otimes e^{\,i\eta(\hat s^{*}-s_0)/(2\pi)}-\hat 1\Big)|\Psi_P\rangle\Big\|^2\;\le\;\frac{\eta^2}{4\pi^2}\,\operatorname{Tr}\!\big[\rho_P(\hat s-s_0)^2\big].$$
--
--   **Role in the source.** This is the state-distance step behind the boost bound (5.32). Because an overall phase drops out of expectation values, the change of a bounded observable $\hat O$ in the normalized state $|\Psi_P\rangle$ under the relative boost is at most $2\|\hat O\|$ times the distance bounded here. This gives $|\langle\hat O\rangle_{\eta,P}-\langle\hat O\rangle_{0,P}|\le\frac{|\eta|}{\pi}\|\hat O\|\sqrt{\operatorname{Tr}[\rho_P(\hat s-s_0)^2]}$, which §5.2 uses in its argument that the diamond Hilbert space is finite-dimensional.
--
--   **Formalization note.**
--   - *Finite dimension.* The paper states (D.23) on the diamond Hilbert space $\mathcal H_D$, with $P$ of finite rank. Here $\mathcal H_D$ is replaced by $\mathbb{C}^n$ for an arbitrary finite index type `n`, so this is the finite-dimensional case of the paper's statement. Vectors of $H\otimes\bar H$ are functions on `n × n`, and $\hat 1\otimes U$ is the Kronecker product `1 ⊗ₖ U`. The norm squared is $\sum_{a,b}|w(a,b)|^2$.
--   - *Conjugate copy.* The paper pairs $|i\rangle$ with its time reflection $|i^*\rangle$ "on the oppositely oriented copy of $S$". This is modelled by entrywise complex conjugation in a fixed basis, $v_i^*=\overline{v_i}$, and correspondingly $\hat s^*=\overline{\hat s}$ (the area operator on the conjugate copy). This is the convention under which the paper's left-hand side, an operator on $\bar H$, is compared with $\operatorname{Tr}[\rho_P(\hat s-s_0)^2]$, a quantity on $H$.
--   - *Normalization.* The paper presupposes $Z>0$. Since $Z=\operatorname{Tr}(PC^\dagger C)$ is real and nonnegative, the Lean statement writes $\sqrt{Z}$ as `Real.sqrt Z.re` and takes the real part of the (real) trace on the right. If $Z=0$, then $\Psi_P=0$ and $\rho_P=0$ in Lean (division by zero is $0$), and the inequality reads $0\le 0$. No hypothesis $Z>0$ is imposed, so the statement is slightly more general than the source.
--   - *Matrix exponential.* This is `NormedSpace.exp` on `Matrix n n ℂ`. The factor $i\eta/(2\pi)$ is written as `Complex.I * ((η / (2 * Real.pi) : ℝ) : ℂ)`. The overall phase $e^{-i\eta s_0/(2\pi)}$ that the paper removes before (D.23) is already absorbed into $\hat s^{*}-s_0$, exactly as in the displayed equation.
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, Appendix D.2, p. 72, eq. (D.23); doubled state eq. (D.22) p. 71; rho_P defined in eq. (5.32) p. 41.

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Matrix Kronecker

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), App. D.2, eq. (D.23), in finite dimension. -/
theorem boost_distance_D23 {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (C s : Matrix n n ℂ) (hs : s.IsHermitian)
    (v : ι → n → ℂ) (hv : ∀ i j, star (v i) ⬝ᵥ v j = if i = j then 1 else 0)
    (s₀ η : ℝ) :
    let P : Matrix n n ℂ := ∑ i, vecMulVec (v i) (star (v i))
    let Z : ℂ := (P * Cᴴ * C).trace
    let ρ : Matrix n n ℂ := Z⁻¹ • (P * Cᴴ * C * P)
    let Ψ : n × n → ℂ := fun ab =>
      (∑ i, (C *ᵥ v i) ab.1 * star (v i ab.2)) / ((Real.sqrt Z.re : ℝ) : ℂ)
    let sStar : Matrix n n ℂ := s.map star
    let U : Matrix n n ℂ :=
      NormedSpace.exp ((Complex.I * ((η / (2 * Real.pi) : ℝ) : ℂ)) • (sStar - (s₀ : ℂ) • 1))
    ∑ ab, ‖(((1 : Matrix n n ℂ) ⊗ₖ U - 1) *ᵥ Ψ) ab‖ ^ 2
      ≤ η ^ 2 / (4 * Real.pi ^ 2) * (ρ * (s - (s₀ : ℂ) • 1) ^ 2).trace.re := by sorry

end ChandrasekaranNullCone
