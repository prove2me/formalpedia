-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_4_2
-- name    : DistQuantumQuery.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:57.374213+00:00
-- url     : https://prove2.me/theorems/3311ac61-5f6f-44f0-8451-18253c47b944
-- title:
--   Proposition 4.2 — primal, dual and vector forms of $\bar\gamma^\mu_2(B\mid\{Z_i\})$
-- statement:
--   Let $\Sigma$ be a finite set, $B\in\mathrm{Herm}(\Sigma)$, and $Z_1,\dots,Z_n\in\mathbb R^{\Sigma\times\Sigma}$ symmetric non-zero matrices. For every distribution $\mu$ on $\Sigma$,
--   $$
--   \begin{aligned}
--   \bar\gamma^\mu_2(B\mid\{Z_i\})&=\max_{\Gamma=\Gamma^\dagger}\ \langle\Gamma,B\circ|\mu\rangle\langle\mu|\rangle\quad\text{s.t. }-I\preceq\Gamma\circ Z_i\preceq I\ \ \forall i\\
--   &=\min_{H_i=H_i^\dagger}\ \sum_i\|H_i\circ|\mu\rangle\langle\mu|\|_{\mathrm{tr}}\quad\text{s.t. }B(x,y)=\sum_iZ_i(x,y)H_i(x,y)\ \ \forall x,y\in\mathrm{supp}(\mu)\\
--   &=\min_d\ \min\ \tfrac12\sum_i\mathbb E_{x\sim\mu}\big[\|u^i_x\|^2+\|v^i_x\|^2\big]\quad\text{s.t. }B(x,y)=\sum_iZ_i(x,y)\langle u^i_x|v^i_y\rangle\ \ \forall x,y\in\mathrm{supp}(\mu),
--   \end{aligned}
--   $$
--   with $|u^i_x\rangle,|v^i_x\rangle\in\mathbb C^d$. Moreover, if $B$ and the $Z_i$ are real, all matrix and vector variables may be taken real.
--
--   The minimization forms give certificates for upper bounds; the vector form feeds the state-conversion algorithm (Proposition 4.8).
--
--   **Formalization Note** Each form is a value in $[0,\infty]$ (an infeasible minimization is $\infty$, as in the proof's convention for $\bar\gamma_2=\infty$), and each optimum is attained whenever $\bar\gamma_2$ is finite. The vectors are given for every $x$; only $x\in\mathrm{supp}(\mu)$ enters the constraints and, with weight $\mu(x)$, the objective.
--
--   Differences from the source:
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: the real number ⟨Γ, M⟩ for Hermitian Γ and Hermitian M (or Tr of a PSD matrix) → the real part of ⟨Γ, M⟩ (resp. of the trace); reason: the inner product is real under the stated hypotheses
--   - encoding: u^i_x, v^i_x for x ∈ supp(μ) → u^i_x, v^i_x for every x ∈ Σ; reason: values off supp(μ) enter neither the constraints nor (weight μ(x) = 0) the objective
--   - encoding: “max”/“min” (attained when the value is finite) → ⨆/⨅ equalities in ℝ≥0∞ plus, when γ̄₂ ≠ ⊤, an attaining feasible point; reason: attainment written out; an infeasible program has value ⊤ as in the proof
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 4.2, p.36

import Mathlib
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 4.2** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 4.2, p.36). Let `Σ` be finite, `B ∈ Herm(Σ)` and
`Z_1, …, Z_n` real symmetric non-zero matrices. For every distribution `μ` on `Σ`,
`γ̄^μ₂(B | {Z_i})`
`= max_{Γ = Γ†} ⟨Γ, B ∘ |μ⟩⟨μ|⟩ s.t. −I ⪯ Γ ∘ Z_i ⪯ I ∀ i`
`= min_{H_i = H_i†} Σ_i ‖H_i ∘ |μ⟩⟨μ|‖_tr s.t. B(x,y) = Σ_i Z_i(x,y) H_i(x,y) ∀ x, y ∈ supp μ`
`= min_d min ½ Σ_i E_{x∼μ}[‖u^i_x‖² + ‖v^i_x‖²] s.t. B(x,y) = Σ_i Z_i(x,y)⟨u^i_x|v^i_y⟩ ∀ x, y ∈ supp μ`,
with `u^i_x, v^i_x ∈ ℂ^d`. Moreover, if `B` and the `Z_i` are real, all variables may be taken
real.

**Formalization Note** Every form is an `ℝ≥0∞` value: the maximum a supremum, the minima infima
(`⊤` on an infeasible program, the proof's convention "all values are understood to be +∞"
when `γ̄₂ = +∞`); each is attained whenever `γ̄₂` is finite. The objective `⟨Γ, B ∘ |μ⟩⟨μ|⟩` is
real for Hermitian `Γ, B`; its real part is used. The vectors `u^i_x, v^i_x` are given for all
`x`; only `x ∈ supp μ` enters. Real variables: `Γ`, `H_i` with real entries, and `u, v` with
real coordinates. -/
theorem proposition_4_2 {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P]
    (B : Matrix X X ℂ) (hB : B.IsHermitian) (Z : P → Matrix X X ℂ)
    (hZreal : ∀ i x y, (Z i x y).im = 0) (hZsymm : ∀ i, (Z i)ᵀ = Z i) (hZ0 : ∀ i, Z i ≠ 0)
    (μ : X → ℝ) (hμ : IsDist μ) :
    let primalFeas : Matrix X X ℂ → Prop := fun Γ => Γ.IsHermitian ∧
      ∀ i, ((1 : Matrix X X ℂ) - Γ ⊙ Z i).PosSemidef ∧ (Γ ⊙ Z i + 1).PosSemidef
    let primalObj : Matrix X X ℂ → ℝ≥0∞ := fun Γ => ENNReal.ofReal (hsInner Γ (B ⊙ muMat μ)).re
    let dualFeas : (P → Matrix X X ℂ) → Prop := fun H => (∀ i, (H i).IsHermitian) ∧
      ∀ x y, 0 < μ x → 0 < μ y → B x y = ∑ i, Z i x y * H i x y
    let dualObj : (P → Matrix X X ℂ) → ℝ≥0∞ := fun H =>
      ENNReal.ofReal (∑ i, traceNorm (H i ⊙ muMat μ))
    let vecFeas : (d : ℕ) → (P → X → Fin d → ℂ) → (P → X → Fin d → ℂ) → Prop := fun _ u v =>
      ∀ x y, 0 < μ x → 0 < μ y → B x y = ∑ i, Z i x y * (star (u i x) ⬝ᵥ v i y)
    let vecObj : (d : ℕ) → (P → X → Fin d → ℂ) → (P → X → Fin d → ℂ) → ℝ≥0∞ := fun _ u v =>
      ENNReal.ofReal ((1 / 2) * ∑ i, ∑ x, μ x *
        (∑ k, Complex.normSq (u i x k) + ∑ k, Complex.normSq (v i x k)))
    let isReal : Matrix X X ℂ → Prop := fun M => ∀ x y, (M x y).im = 0
    let isRealVec : {d : ℕ} → (P → X → Fin d → ℂ) → Prop := fun u => ∀ i x k, (u i x k).im = 0
    -- the three forms
    (gammaBar μ B Z = ⨆ (Γ : Matrix X X ℂ) (_ : primalFeas Γ), primalObj Γ) ∧
    (gammaBar μ B Z ≠ ⊤ → ∃ Γ, primalFeas Γ ∧ primalObj Γ = gammaBar μ B Z) ∧
    (gammaBar μ B Z = ⨅ (H : P → Matrix X X ℂ) (_ : dualFeas H), dualObj H) ∧
    (gammaBar μ B Z ≠ ⊤ → ∃ H, dualFeas H ∧ dualObj H = gammaBar μ B Z) ∧
    (gammaBar μ B Z = ⨅ (d : ℕ) (u : P → X → Fin d → ℂ) (v : P → X → Fin d → ℂ)
        (_ : vecFeas d u v), vecObj d u v) ∧
    (gammaBar μ B Z ≠ ⊤ → ∃ (d : ℕ) (u v : P → X → Fin d → ℂ), vecFeas d u v ∧
        vecObj d u v = gammaBar μ B Z) ∧
    -- Moreover: real data admit real variables
    ((∀ x y, (B x y).im = 0) →
      (gammaBar μ B Z = ⨆ (Γ : Matrix X X ℂ) (_ : primalFeas Γ ∧ isReal Γ), primalObj Γ) ∧
      (gammaBar μ B Z ≠ ⊤ → ∃ Γ, primalFeas Γ ∧ isReal Γ ∧ primalObj Γ = gammaBar μ B Z) ∧
      (gammaBar μ B Z = ⨅ (H : P → Matrix X X ℂ) (_ : dualFeas H ∧ ∀ i, isReal (H i)),
        dualObj H) ∧
      (gammaBar μ B Z ≠ ⊤ → ∃ H, dualFeas H ∧ (∀ i, isReal (H i)) ∧
        dualObj H = gammaBar μ B Z) ∧
      (gammaBar μ B Z = ⨅ (d : ℕ) (u : P → X → Fin d → ℂ) (v : P → X → Fin d → ℂ)
          (_ : vecFeas d u v ∧ isRealVec u ∧ isRealVec v), vecObj d u v) ∧
      (gammaBar μ B Z ≠ ⊤ → ∃ (d : ℕ) (u v : P → X → Fin d → ℂ), vecFeas d u v ∧
          isRealVec u ∧ isRealVec v ∧ vecObj d u v = gammaBar μ B Z)) := by sorry

end DistQuantumQuery
