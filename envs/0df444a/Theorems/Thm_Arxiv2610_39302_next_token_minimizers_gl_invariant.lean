-- Prove2me | Theorems.Thm_Arxiv2610_39302_next_token_minimizers_gl_invariant
-- name    : Arxiv2610_39302.next_token_minimizers_gl_invariant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:07:20.497967+00:00
-- url     : https://prove2.me/theorems/64346fc3-5019-5401-bc5a-62316366e046
-- title:
--   Proposition 4 (iii) (as proved): next-token minimizers are identified only up to $\mathrm{GL}(k)$
-- statement:
--   Let finitely many contexts $c$ have probabilities $P(c)>0$, and let every conditional $p(\cdot\mid c)$ on a finite vocabulary $V$ have full support. Consider the expected next-token loss
--
--   $$\mathcal R(h,w)=\sum_cP(c)\sum_vp(v\mid c)\Big(-\log\mathrm{softmax}\big(\langle h(c),w_v\rangle\big)_{v}\Big)$$
--
--   over context embeddings $h(c)\in\mathbb{R}^k$ and token vectors $w_v\in\mathbb{R}^k$. Suppose $k$ is at least the rank of the matrix $[\log p(v\mid c)]_{v,c}$ modulo constants, i.e. $\operatorname{rank}[\log p(v\mid c)+b(c)]_{v,c}\le k$ for some $b$. Then:
--
--   1. $(h,w)$ minimises $\mathcal R$ if and only if $\langle h(c),w_v\rangle=\log p(v\mid c)+b(c)$ for all $c,v$, for some $b$;
--   2. the logits are unchanged by $h\mapsto Gh$, $w\mapsto G^{-\top}w$ for every invertible $G\in\mathrm{GL}(k)$;
--   3. hence the set of minimisers is invariant under $\mathrm{GL}(k)$: if $(h,w)$ is a minimiser, so is $(Gh,G^{-\top}w)$.
--
--   **Formalization Note** The printed hypothesis "$k$ large enough" is replaced by the condition the proof uses: $k$ at least the rank of $[\log p(v\mid c)]$ modulo constants. The paper does not define the objective whose minimisers are meant; it is taken as the expected loss over finitely many contexts with positive weights, which is the reading under which the rank condition matters (the table $w$ is shared by all contexts). The paper's conclusion that $h$ is identified at best up to an invertible linear map, not a rotation, is an interpretation of item 3; the Lean statement does not assert that some non-orthogonal $G$ yields a genuinely different minimiser.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c012; Section 2.4, Proposition 4 (iii), PDF p. 6; proof in Appendix A.5, PDF p. 23

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem next_token_minimizers_gl_invariant {C V : Type*} [Fintype C] [Fintype V] [Nonempty V]
    {k : ℕ} (P : C → ℝ) (hP : ∀ c, 0 < P c) (hP1 : ∑ c, P c = 1)
    (cond : C → V → ℝ) (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (hrank : ∃ b : C → ℝ, (Matrix.of fun (v : V) (c : C) => Real.log (cond c v) + b c).rank ≤ k) :
    (∀ (h : C → Fin k → ℝ) (w : V → Fin k → ℝ),
      (∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond h w ≤ ntpRisk P cond h' w') ↔
        ∃ b : C → ℝ, ∀ c v, h c ⬝ᵥ w v = Real.log (cond c v) + b c) ∧
    (∀ (G : Matrix.GeneralLinearGroup (Fin k) ℝ) (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) c v,
      ((G : Matrix (Fin k) (Fin k) ℝ) *ᵥ h c) ⬝ᵥ
          ((((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ w v) =
        h c ⬝ᵥ w v) ∧
    (∀ (G : Matrix.GeneralLinearGroup (Fin k) ℝ) (h : C → Fin k → ℝ) (w : V → Fin k → ℝ),
      (∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond h w ≤ ntpRisk P cond h' w') →
      ∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond (fun c => (G : Matrix (Fin k) (Fin k) ℝ) *ᵥ h c)
          (fun v => (((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ w v)
        ≤ ntpRisk P cond h' w') := by sorry

end Arxiv2610_39302
