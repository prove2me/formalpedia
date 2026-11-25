-- Prove2me | Theorems.Thm_Arxiv1901_08703_mixed_reciprocity_as_proved
-- name    : Arxiv1901_08703.mixed_reciprocity_as_proved
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:26:23.290716+00:00
-- url     : https://prove2.me/theorems/a1d97f96-03b0-425c-8e7b-51a067619b7f
-- title:
--   Lemma 4.2 (as proved): the mixed reciprocity relation
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support and $k>0$. Let $y\in D_+$ be such that its reflection $y^{re}=(y_1,-y_2)$ lies in $D_-$, and let $d\in\mathbb S^1_+$. Let $u^s(\cdot;y)$ solve (NP) with data $f(\cdot;y)=-\partial_\nu\big(\Phi_k(\cdot,y)+\Phi_k(\cdot,y^{re})\big)$ on $\Gamma$, and let $u^s(\cdot;-d)$ solve (NP) for the incident plane wave of direction $-d\in\mathbb S^1_-$. Write $u(x;y)=\Phi_k(x,y)+\Phi_k(x,y^{re})+u^s(x;y)$ and $u(x;-d)=u^i(x;-d)+u^r(x;-d)+u^s(x;-d)$ for the total fields. If $u^\infty(\cdot;y)$ is the far-field pattern on $\mathbb S^1_+$ of the total field $u(\cdot;y)$, then
--   $$u^\infty(d;y)=\gamma\,u(y;-d),\qquad\gamma=\frac{e^{i\pi/4}}{\sqrt{8k\pi}}.$$
--
--   **Formalization Note** This is the statement the proof establishes, not the printed one. Lemma 4.2 as printed calls $u^\infty(\cdot;y)$ the far-field pattern of the scattered field $u^s(\cdot;y)$, and it is then false. For the flat surface $h=0$, $u^s(\cdot;y)=0$ but $\gamma u(y;-d)=\gamma(e^{-ikd\cdot y}+e^{-ikd\cdot y^{re}})\ne0$ in general. The proof applies Colton–Kress (3.87) to the total field $u(\cdot;y)$, eq. (4.4), so it computes the far-field pattern of $u(\cdot;y)$. Equivalently, the far-field pattern of $u^s(\cdot;y)$ at $d$ equals $\gamma u^s(y;-d)$. The proof's Green's formula (4.1) excises only a small disc around $y$, so it requires $\Phi_k(\cdot,y^{re})$ to be regular in $\overline{D_+}$. The hypothesis $y^{re}\in D_-$ is added for this reason.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c014; Section 4, Lemma 4.2 and its proof, eqs. (4.1)-(4.4), PDF pp. 19-20

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem mixed_reciprocity_as_proved (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : IsLocalProfile h)
    (y : R2) (hy : y ∈ Dplus h) (hyre : refl y ∈ Dminus h) (d : R2) (hd : d ∈ upperCircle)
    (usy : R2 → ℂ) (husy : IsNPSolution k h (pointData k h y) usy)
    (usd : R2 → ℂ) (husd : IsNPSolution k h (incData k (-d) h) usd)
    (F : R2 → ℂ)
    (hF : HasFarFieldOn k (fun x => Phi k x y + Phi k x (refl y) + usy x) F upperCircle) :
    F d = gammaInf k * (uInc k (-d) y + uRefl k (-d) y + usd y) := by sorry

end Arxiv1901_08703
