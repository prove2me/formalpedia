-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq
-- name    : AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/1a757678-5367-5153-b2ed-ce046decb60e
-- title:
--   A linear right inverse of the split transform at weight zero
-- statement:
--   Let $P$ be a real normed space. The assertion is the existence of an operator $I$ sending complex-valued functions of a pair of reals to complex-valued functions of a real $2\times 2$ array of entries, with the following two properties. First, $I$ is linear on smooth compactly supported data: for all smooth $f,g:\mathbb R\times\mathbb R\to\mathbb C$ with compact support and all $a,b\in\mathbb C$, $I(af+bg)=aI(f)+bI(g)$ pointwise in the matrix variable. Second, for every $H:\mathbb R\times\mathbb R\times P\to\mathbb C$ that is smooth, compactly supported, has $\operatorname{tsupport} H$ contained in $\{a_1a_2\neq 0\}$, is symmetric, $H(a_2,a_1,p)=H(a_1,a_2,p)$, and even, $H(-a_1,-a_2,p)=H(a_1,a_2,p)$, the family $F(M,p):=I\big(H(\cdot,\cdot,p)\big)(M)$ satisfies: $F$ is smooth and compactly supported on $(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R)\times P$; $\operatorname{tsupport} F$ is contained in the set of pairs whose matrix has invertible determinant; for each $p$ the slice $g\mapsto F(\text{entries of }g,p)$ on $\mathrm{GL}_2(\mathbb R)$ transforms under $k_1,k_2$ in the subgroup `rowIsometrySubgroup₀ ℝ` by the scalar $\mathrm{archWeightChar}_{\mathbb R}(0)(k_1)\cdot\mathrm{archWeightChar}_{\mathbb R}(0)(k_2)$, i.e. $F(k_1gk_2,p)$ equals that scalar times $F(g,p)$; and for all $p$ and all $a_1a_2\neq 0$ the split transform of that slice at $(a_1,a_2)$ — the average $\frac1{2\pi}\int_0^{2\pi}\!\!\int_{\mathbb R} F\big(r_\theta\,\begin{pmatrix}a_1&u\\0&a_2\end{pmatrix}\,r_\theta^{-1},p\big)\,du\,d\theta$ over rotations $r_\theta$, and $0$ on the axes — equals $H(a_1,a_2,p)$.
--
--   This is the archimedean weight-zero surjectivity statement for the split orbital transform on $\mathrm{GL}_2(\mathbb R)$: even symmetric split data supported away from the axes are realised, linearly and uniformly in a parameter space $P$, as split transforms of smooth compactly supported functions with the prescribed bi-invariance type. It is used by the weight-one analogue and by the construction of test functions pairing with discrete series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ),
      (∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M) ∧
      ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H → tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
        (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
        (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = H (a₁, a₂, p)) →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
          {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
        (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
              ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
            ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) *
              entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
        ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
          splitTransform
              (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
              a₁ a₂ =
            H (a₁, a₂, p) := by sorry
