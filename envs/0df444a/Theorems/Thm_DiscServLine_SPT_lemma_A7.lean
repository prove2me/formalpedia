-- Prove2me | Theorems.Thm_DiscServLine_SPT_lemma_A7
-- name    : DiscServLine.SPT.lemma_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:31.165244+00:00
-- url     : https://prove2.me/theorems/5344f61c-ed2e-43bc-86f1-6e2267f534b7
-- title:
--   Lemma A7, Suppl. pp. 22–23 (PDF 69–70) — the optimal SPT service line in closed form through a root ω of (A–35)
-- statement:
--   Assume $0<c<\bar\theta$, $b>0$, $\Lambda>0$, and put $\kappa=2b/(\Lambda c)$. Then problem (9), maximize $(\bar\theta\Lambda_1-b\Lambda_2)-c(\Lambda_1+Q)$ over feasible service lines, has an optimal solution, and every optimal service line is given by a root $\omega\in(0,1)$ of (A–35), $F(\omega)=0$, through
--   $$\Lambda_0=\Lambda,\qquad \Lambda_1=1-\sqrt\omega,\qquad \Lambda_2=2\frac{c}{4b}\Big(\frac{\bar\theta}{c}-1\Big)\sqrt\omega\Big(\sqrt{\frac{1+\kappa}{1+\omega\kappa}}-1\Big),$$
--   $$\underline t=\frac{c}{2b}\sqrt{1+\kappa}\,\big(\sqrt{1+\kappa}-\sqrt{1+\omega\kappa}\big),\qquad \bar t=\frac{c}{2b}\,\frac{\sqrt{1+\kappa}-\sqrt{1+\omega\kappa}}{\sqrt{\omega/(1+\omega\kappa)}} .$$
--
--   This is the paper's explicit solution of the homogeneous-customer SPT problem; the structural statements of Proposition 5 are read off from it.
--
--   **Formalization Note** "Is given by $\omega$, the solution to (A–35)" is read as "for some root $\omega\in(0,1)$"; uniqueness of the root is not claimed. Existence of an optimal service line, presupposed by the lemma, is stated explicitly. The objective is eq. (9), $(\bar\theta-c)\Lambda_1-b\Lambda_2-cQ$; the lemma's printed objective omits the term $-c\Lambda_1$, which its proof includes through $m=\bar\theta/c-1$.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), Supplementary Document, pp. 22–23 (PDF 69–70), Lemma A7 and (A–35)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem lemma_A7 (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧
      ∀ d, IsOptimal P d → ∃ ω ∈ Set.Ioo (0 : ℝ) 1, F35 P ω = 0 ∧
        d.Λk 0 = P.Λ ∧ d.Λk 1 = 1 - Real.sqrt ω ∧ d.Λk 2 = Λ2A7 P ω ∧
        d.lo = tLoA7 P ω ∧ d.hi = tHiA7 P ω := by sorry

end DiscServLine.SPT
