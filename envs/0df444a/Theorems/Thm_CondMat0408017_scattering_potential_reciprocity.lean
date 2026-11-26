-- Prove2me | Theorems.Thm_CondMat0408017_scattering_potential_reciprocity
-- name    : CondMat0408017.scattering_potential_reciprocity
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:22:29.58827+00:00
-- url     : https://prove2.me/theorems/ddfe6055-b73d-57b4-8bd1-acfc745617fd
-- title:
--   Text after eq. (97): the first- and second-order scattering potentials are reciprocal
-- statement:
--   Let $\varepsilon$ be complex, $w=\omega/c$, let $\alpha(q)$ be even, $\alpha(-q)=\alpha(q)$, and let $\tilde\zeta^{(1)},\tilde\zeta^{(2)}$ be any complex functions. Let $V^{(1)}_\nu,V^{(2)}_\nu$ be the first- and second-order scattering potentials (97):
--
--   $$V^{(1)}_p(q|k)=i\frac{\varepsilon-1}{\varepsilon^2}[\varepsilon qk-\alpha(q)\alpha(k)]\tilde\zeta^{(1)}(q-k),\qquad V^{(1)}_s(q|k)=iw^2(\varepsilon-1)\tilde\zeta^{(1)}(q-k),$$
--
--   $$V^{(2)}_p(q|k)=i\frac{\varepsilon-1}{\varepsilon^2}[\alpha(q)+\alpha(k)][qk-\alpha(q)\alpha(k)]\tilde\zeta^{(2)}(q-k)+2i\frac{(\varepsilon-1)^2}{\varepsilon^3}\alpha(q)\int\frac{dp}{2\pi}\tilde\zeta^{(1)}(q-p)\alpha(p)\tilde\zeta^{(1)}(p-k)\,\alpha(k),$$
--
--   $$V^{(2)}_s(q|k)=iw^2(\varepsilon-1)[\alpha(q)+\alpha(k)]\tilde\zeta^{(2)}(q-k).$$
--
--   Then for $n=1,2$, $\nu=p,s$ and all $q,k$, $V^{(n)}_\nu(q|k)=V^{(n)}_\nu(-k|-q)$: the potentials are reciprocal.
--
--   **Formalization Note** The expressions (97) are quoted from Maradudin and Méndez (1993). The claim is that they are manifestly reciprocal. It uses only the evenness of $\alpha(q)=\sqrt{\varepsilon\omega^2/c^2-q^2}$, so $\tilde\zeta^{(1)},\tilde\zeta^{(2)}$ are arbitrary. The integral is a Lebesgue integral. The paper's further remark that reciprocity holds to all orders is cited from Brown et al. (1984) and is not part of the statement.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c049; Sec. III.G.2, eq. (Eq:Scattering-pot) [(97)] and the text after it, PDF p. 31

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem scattering_potential_reciprocity (ν : Polarization) (eps : ℂ) (wv : ℝ)
    (α ζ1 ζ2 : ℝ → ℂ) (hα : ∀ q, α (-q) = α q) (q k : ℝ) :
    scatPotV1 ν eps wv α ζ1 q k = scatPotV1 ν eps wv α ζ1 (-k) (-q) ∧
      scatPotV2 ν eps wv α ζ1 ζ2 q k = scatPotV2 ν eps wv α ζ1 ζ2 (-k) (-q) := by sorry

end CondMat0408017
