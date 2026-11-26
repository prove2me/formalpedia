-- Prove2me | Theorems.Thm_Arxiv2405_10327_weak_form_decouples_forward_operator
-- name    : Arxiv2405_10327.weak_form_decouples_forward_operator
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T17:55:46.653668+00:00
-- url     : https://prove2.me/theorems/96a9534e-2809-4cb6-8144-1b31350b32ca
-- title:
--   Section 3, eq. (2) and Algorithm 1: the weak form decouples the forward operator from the networks
-- statement:
--   Let $M\ge1$, $\sigma>0$ and $\gamma>0$. Let $\mathcal F:\mathbb{R}^d\to\mathbb{R}^m$ be the forward operator and $y_{\mathrm{obs}}$ the observed data. Let $f_{\theta^*}^{-1}(\cdot\,;c)$ be invertible for every conditioning $c$, and let every refinement network $h_\phi$, $\phi\in\mathbb{R}^p$, be invertible and differentiable. Fix latent draws $z_1,\dots,z_M$ and write $J_\gamma$ for the weak objective of eq. (2) and $\mathcal L$ for the inner-loop loss of Algorithm 1, line 29. Then:
--
--   1. The forward operator enters $J_\gamma$ only through the data-misfit terms: for all velocity models $x_{1:M}$ and weights $\phi$,
--   $$J_\gamma(x_{1:M},\phi)=\frac1M\sum_{i=1}^M\frac{1}{2\sigma^2}\|\mathcal F(x_i)-y_{\mathrm{obs}}\|_2^2+\frac1M\,\mathcal L(\phi;x_{1:M}),$$
--   where $\mathcal L$ does not involve $\mathcal F$.
--   2. For fixed $x_{1:M}$, the gradient of $J_\gamma$ in $\phi$ is $\frac1M\nabla_\phi\mathcal L(\phi;x_{1:M})$.
--   3. For fixed $x_{1:M}$, $\phi$ minimises $J_\gamma(x_{1:M},\cdot)$ if and only if it minimises $\mathcal L(\cdot\,;x_{1:M})$.
--   4. For fixed $\phi$ and the other models, the gradient of $J_\gamma$ in $x_i$ is $\frac1M g_i$, where $g_i$ is the gradient of line 25 of Algorithm 1:
--   $$g_i=\nabla_{x_i}\Big[\frac1{2\sigma^2}\|\mathcal F(x_i)-y_{\mathrm{obs}}\|_2^2+\frac1{2\gamma^2}\|x_i-f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})\|_2^2\Big].$$
--
--   This is the mathematical content of the paper's statement that the weak formulation decouples $\mathcal F$ from the networks. The inner loop of WISER, which updates $\phi$, needs no wave modelling, and $\mathcal F$ enters only the outer gradient steps on the velocity models.
--
--   **Formalization Note** Gradients are Mathlib's `gradient`, which is $0$ at points of non-differentiability. Items 2 and 4 are therefore stated without differentiability hypotheses, and both sides vanish together where the functions are not differentiable. The paper's claim that the inner loop "needs no physics modelling" is formalised by items 1-3: the inner-loop loss is defined without $\mathcal F$ and has the same minimisers and, up to the factor $1/M$, the same gradient in $\phi$ as eq. (2). Algorithm 1 omits the factor $1/M$ in lines 25 and 29.
-- source:
--   Yin, Orozco and Herrmann, WISER: multimodal variational inference for full-waveform inversion without dimensionality reduction, arXiv:2405.10327v2 (2024), claim c002; Section 3 (Physics-based refinements), eq. (2) and the paragraphs after it, Algorithm 1 lines 22-32, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2405_10327_Basic

open Filter Topology

namespace Arxiv2405_10327

theorem weak_form_decouples_forward_operator {d m p M : ℕ} {C : Type*}
    (hM : 0 < M) (σ γ : ℝ) (hσ : 0 < σ) (hγ : 0 < γ)
    (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (hfInv : ∀ c, Function.Bijective (fun u => fInv u c))
    (h : Vec p → Vec d → Vec d) (hh : ∀ φ, Function.Bijective (h φ) ∧ Differentiable ℝ (h φ))
    (z : Fin M → Vec d) :
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjective σ γ F yobs fInv ybar h z x φ =
        (1 / (M : ℝ)) * (∑ i, dataMisfit σ F yobs (x i))
          + (1 / (M : ℝ)) * innerLoss γ fInv ybar h z x φ) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      gradient (fun φ' => weakObjective σ γ F yobs fInv ybar h z x φ') φ =
        (1 / (M : ℝ)) • gradient (fun φ' => innerLoss γ fInv ybar h z x φ') φ) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      (∀ φ', weakObjective σ γ F yobs fInv ybar h z x φ ≤ weakObjective σ γ F yobs fInv ybar h z x φ') ↔
        (∀ φ', innerLoss γ fInv ybar h z x φ ≤ innerLoss γ fInv ybar h z x φ')) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p) (i : Fin M),
      gradient (fun v => weakObjective σ γ F yobs fInv ybar h z (Function.update x i v) φ) (x i) =
        (1 / (M : ℝ)) • gradient (outerLoss σ γ F yobs fInv ybar (h φ) (z i)) (x i)) := by sorry

end Arxiv2405_10327
