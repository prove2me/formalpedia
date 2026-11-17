-- Prove2me | Theorems.Thm_DimFreeShadow_Supplement_theorem_2_4
-- name    : DimFreeShadow.Supplement.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:00:29.963263+00:00
-- url     : https://prove2.me/theorems/47c68bb7-4439-4e9d-a5b5-8ef57f69c301
-- title:
--   Theorem 2.4 — the PGM decoded as $z_Y$ has at most twice the optimal mean-square risk
-- statement:
--   Let $\mathcal F=\{(q_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble of states on a finite-dimensional Hilbert space $\mathcal H$, with $q_x>0$ and $\sum_xq_x=1$, and let $\{G_y\}_{y\in\mathcal X}$ be its completed pretty-good measurement (one copy). Assign an arbitrary real label $z_x$ to each state. A **scalar estimation strategy** is a POVM $\{N_w:w\in\mathcal W\}$ on $\mathcal H$ together with reported values $\hat z_w\in\mathbb R$; its mean-square risk is $\sum_{x,w}q_x\operatorname{Tr}(N_w\rho_x)(z_x-\hat z_w)^2$.
--
--   **Theorem.** If the PGM outcome $Y$ is decoded as $z_Y$, then
--
--   $$
--   \sum_{x,y}q_x\operatorname{Tr}(G_y\rho_x)(z_x-z_y)^2\ \le\ 2\inf_{\{N_w\},\{\hat z_w\}}\ \sum_{x,w}q_x\operatorname{Tr}(N_w\rho_x)(z_x-\hat z_w)^2 .
--   $$
--
--   The PGM is determined entirely by $\mathcal F$ and does not depend on the labels $z$.
--
--   This is the finite-dimensional quadratic case of a theorem of Mishra, Lami and Wilde: one label-independent measurement estimates every scalar function of the label within a factor two of the Bayes-optimal (Personick) risk. Section 3 applies it round by round with recursively changed labels.
--
--   **Formalization Note** "$\le2\inf$" is stated as "$\le2\times$ the risk of every strategy" (every finite outcome type $\mathcal W$, POVM and reported values), which is equivalent since the risks form a nonempty set bounded below by $0$. Traces enter through their real parts.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: LHS ≤ 2 inf over all strategies ({N_w}, {ẑ_w}) → LHS ≤ 2 × the risk of each strategy; reason: the set of risks is nonempty and bounded below by 0, so the two are equivalent
--   - reading: a POVM {N_w : w ∈ W} with unspecified outcome set W → W any finite type; reason: POVMs on a finite-dimensional space in the paper are finite-outcome, and by Proposition 2.3 the infimum is attained by a finite spectral PVM, so the infimum is the same
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 2.4, p.11; risk Eq. (8), p.10; Definition 2.1, pp.5–6

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DimFreeShadow_Supplement_pgmEffect

namespace DimFreeShadow

namespace Supplement

/-- **Theorem 2.4 (the PGM has at most twice the optimal mean-square risk)** (arXiv:2608.06345,
sha256 a1a42249…, Theorem 2.4, p.11; risk Eq. (8), p.10). Let `{(q_x, ρ_x) : x ∈ X}` be a
finite ensemble on `H` (`q_x > 0`, `Σ_x q_x = 1`) and `{G_y}` its completed PGM with `T = 1`
(Definition 2.1). For every real labelling `z : X → ℝ`, if the PGM outcome `Y` is decoded as
`z_Y`, then
`Σ_{x,y} q_x Tr(G_y ρ_x)(z_x − z_y)² ≤ 2 inf_{{N_w},{ẑ_w}} Σ_{x,w} q_x Tr(N_w ρ_x)(z_x − ẑ_w)²`.
The PGM is determined entirely by the ensemble and is independent of the labels `z`.

**Formalization Note** `H = ℂ^d` for a finite type `d`. "`≤ 2 inf`" over all scalar estimation
strategies (any finite outcome type `W`, any POVM `{N_w}` on `H`, any reported values
`ẑ : W → ℝ`) is stated as "`≤ 2 ×` the risk of every such strategy", which is equivalent
because the set of risks is nonempty and bounded below by `0`. `G = pgmEffect q ρ` takes no
label argument. Traces through real parts. -/
theorem theorem_2_4 {X d : Type} [Fintype X] [Fintype d] [DecidableEq d] (q : X → ℝ)
    (hq : ∀ x, 0 < q x) (hq1 : ∑ x, q x = 1) (ρ : X → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (z : X → ℝ) :
    ∀ (W : Type) [Fintype W] (N : W → Matrix d d ℂ), QAlgorithms.IsPOVM N →
      ∀ zhat : W → ℝ,
        ∑ x, ∑ y, q x * (pgmEffect q ρ y * ρ x).trace.re * (z x - z y) ^ 2 ≤
          2 * ∑ x, ∑ w, q x * (N w * ρ x).trace.re * (z x - zhat w) ^ 2 := by sorry

end Supplement

end DimFreeShadow
