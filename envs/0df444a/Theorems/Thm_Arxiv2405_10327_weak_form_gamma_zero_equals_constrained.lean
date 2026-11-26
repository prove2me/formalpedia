-- Prove2me | Theorems.Thm_Arxiv2405_10327_weak_form_gamma_zero_equals_constrained
-- name    : Arxiv2405_10327.weak_form_gamma_zero_equals_constrained
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:01:00.668293+00:00
-- url     : https://prove2.me/theorems/87a6fa16-1583-5a04-9d67-c725111e32f9
-- title:
--   Section 3, eqs. (1)-(2): setting $\gamma$ to $0$ equates the weak formulation with the constrained formulation (as proved)
-- statement:
--   Let $M\ge1$ and $\sigma>0$. Let $\mathcal F:\mathbb{R}^d\to\mathbb{R}^m$ be the forward operator and $y_{\mathrm{obs}}$ the observed data. Let $f_{\theta^*}^{-1}(\cdot\,;c)$ be invertible for every conditioning $c$, and let every refinement network $h_\phi$, $\phi\in\mathbb{R}^p$, be invertible and differentiable. Fix latent draws $z_1,\dots,z_M$. Write $G_i(\phi)=f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})$, let $J_\gamma$ be the weak objective of eq. (2), and let
--   $$S(\phi)=\frac1M\sum_{i=1}^M\Big[\frac1{2\sigma^2}\|\mathcal F(G_i(\phi))-y_{\mathrm{obs}}\|_2^2+\tfrac12\|h_\phi(z_i)\|_2^2-\log|\det J_{h_\phi}(z_i)|\Big]$$
--   be the constrained objective of eq. (1) evaluated on the same draws. Let $J_0$ be the weak objective with $\gamma$ set to $0$. It equals the $\gamma$-independent terms of eq. (2) when $x_i=G_i(\phi)$ for all $i$, and $+\infty$ otherwise. Then:
--
--   1. For every $(x_{1:M},\phi)$, $J_\gamma(x_{1:M},\phi)\to J_0(x_{1:M},\phi)$ in $(-\infty,+\infty]$ as $\gamma\to0^+$.
--   2. For every $(x_{1:M},\phi)$, $J_0(x_{1:M},\phi)=S(\phi)$ if $x_i=G_i(\phi)$ for all $i$, and $J_0(x_{1:M},\phi)=+\infty$ otherwise.
--   3. The optimal values agree:
--   $$\inf_{x_{1:M},\,\phi}J_0(x_{1:M},\phi)=\inf_\phi S(\phi).$$
--   4. $(x_{1:M},\phi)$ minimises $J_0$ if and only if $x_i=G_i(\phi)$ for every $i$ and $\phi$ minimises $S$.
--
--   This is the paper's statement that setting $\gamma$ to $0$ makes the weak formulation (2) equal to the constrained formulation (1).
--
--   **Formalization Note** The paper's formula (2) is undefined at $\gamma=0$. Setting $\gamma$ to $0$ is formalised as the extended-real objective $J_0$, and item 1 shows that $J_0$ is the pointwise limit of $J_\gamma$. Eq. (1) is an expectation over $z\sim\mathrm N(0,I)$, while eq. (2) uses $M$ fixed draws $z_i$. What the $\gamma=0$ reduction establishes is equality with the $M$-sample average $S$ of the integrand of eq. (1), not with the expectation, so the statement is titled "as proved". The statement is about the objectives at $\gamma=0$. It does not assert that the optimal values of $J_\gamma$ converge to $\inf S$ as $\gamma\to0^+$, which the paper does not claim and which needs further assumptions.
-- source:
--   Yin, Orozco and Herrmann, WISER: multimodal variational inference for full-waveform inversion without dimensionality reduction, arXiv:2405.10327v2 (2024), claim c001; Section 3 (Physics-based refinements), eq. (1), eq. (2) and the sentence after eq. (2), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2405_10327_Basic

open Filter Topology

namespace Arxiv2405_10327

theorem weak_form_gamma_zero_equals_constrained {d m p M : ℕ} {C : Type*}
    (hM : 0 < M) (σ : ℝ) (hσ : 0 < σ)
    (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (hfInv : ∀ c, Function.Bijective (fun u => fInv u c))
    (h : Vec p → Vec d → Vec d) (hh : ∀ φ, Function.Bijective (h φ) ∧ Differentiable ℝ (h φ))
    (z : Fin M → Vec d) :
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      Tendsto (fun γ : ℝ => ((weakObjective σ γ F yobs fInv ybar h z x φ : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 (weakObjectiveHard σ F yobs fInv ybar h z x φ))) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjectiveHard σ F yobs fInv ybar h z x φ =
        if ∀ i, x i = corrected fInv ybar (h φ) (z i) then
          ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal) else ⊤) ∧
    ((⨅ (x : Fin M → Vec d) (φ : Vec p), weakObjectiveHard σ F yobs fInv ybar h z x φ) =
      ⨅ φ : Vec p, ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal)) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      (∀ (x' : Fin M → Vec d) (φ' : Vec p),
          weakObjectiveHard σ F yobs fInv ybar h z x φ ≤ weakObjectiveHard σ F yobs fInv ybar h z x' φ') ↔
        ((∀ i, x i = corrected fInv ybar (h φ) (z i)) ∧
          ∀ φ' : Vec p, strongSampleObjective σ F yobs fInv ybar h z φ ≤
            strongSampleObjective σ F yobs fInv ybar h z φ')) := by sorry

end Arxiv2405_10327
