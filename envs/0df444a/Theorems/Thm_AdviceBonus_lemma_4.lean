-- Prove2me | Theorems.Thm_AdviceBonus_lemma_4
-- name    : AdviceBonus.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:13.765163+00:00
-- url     : https://prove2.me/theorems/ea5fe77e-d26d-4029-9468-fe49bef9003c
-- title:
--   Lemma 4 — the equilibrium commission $f=p-c-2wH(\bar q^A_2)$ (16) (corrected: equilibria with $b<w$)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $p,c\in\mathbb R$ and $w>0$. If $(f,b)$ is a symmetric equilibrium compensation scheme with $f>0$ and $0<b<w$, then
--   $$
--   f=p-c-2w\,H(\bar q^A_2), \qquad(16)
--   $$
--   where $\bar q^A_2$ is the cutoff (2) at the equilibrium profile (the solution of (15), Lemma 3) and
--   $$
--   H(q)=\frac{G(q)}{g(q)}+\frac{1}{4g(1/2)[1-G(q)]^2+g(q)}. \qquad(17)
--   $$
--
--   Since $\bar q^A_2$ does not depend on $w$, the commission falls linearly in the liability.
--
--   Differences from the source:
--   - correction: a symmetric equilibrium with f > 0 and b > 0 → a symmetric equilibrium with f > 0 and 0 < b < w (advice to the second customer informative: q̄A2, q̄B2 ∈ (0, 1)); reason: the printed statement is false: for g ≡ 1, p − c = 1, w = 1/5 the scheme (f, b) = (3/5, 3/5) is a symmetric equilibrium (q̄A2 = 0, q̄B2 = 1; in the lock-in region firm A's profit is (1/2 + (T − 9/5)/(2/5))(2 − T) in T = 2f′ + b′, maximal at T = 9/5 with value 1/10, and a fine grid over X finds no better deviation for either firm), yet (14) would give b = 4G(0)/g(0)·w = 0; the proof (p.32) starts from the interior cutoffs 1/2 ∓ b/(2w), and §3 restricts to informative advice (p.10)
--   - reading: "a symmetric equilibrium" → a symmetric pure Nash equilibrium of the compensation stage at the given price p, strategy set {f ≥ 0, 2f + b ≥ 0}, profits (6); reason: §4 takes p_n = p as given (p.16), and p.8 gives the limited-liability strategy set
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3)
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
--   - generalization: the model's standing assumption (1) on v_h, v_l and c → not assumed; p and c arbitrary reals; reason: §4 takes p as given and (1) only restricts the customer side; the statement specializes to the source's under (1)
--   - encoding: advisor payoffs include w_l → w_l dropped; reason: it cancels from every cutoff
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Lemma 4, eqs. (16)–(17), p.18; proof in Appendix A, p.35

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_AdviceBonus_Equilibrium
import Definitions.Def_AdviceBonus_ClosedForms

namespace AdviceBonus

/-- **Lemma 4**, eqs. (16)–(17), p.18 (Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). In a
symmetric equilibrium with `f_n = f > 0` and `b_n = b > 0` in which
the advice to the second customer is informative (`b < w`, so that `q̄^A_2, q̄^B_2 ∈ (0, 1)`), the commission satisfies
`f = p − c − 2w H(q̄^A_2)`, with `H` from (17) and `q̄^A_2` the cutoff (2) at the equilibrium
profile (the solution of (15), Lemma 3).

**Formalization Note** (corrected) `b < w` is added as in Lemma 2: for `g ≡ 1`, `p − c = 1`,
`w = 1/5`, the symmetric equilibrium `(3/5, 3/5)` has `q̄^A_2 = 0` and `p − c − 2wH(0) = 23/25`. -/
theorem lemma_4 (D : Dist) (p c w : ℝ) (hw : 0 < w) (f b : ℝ)
    (heq : IsSymEq D p c w (f, b)) (hf : 0 < f) (hb : 0 < b) (hbw : b < w) :
    f = p - c - 2 * w * H D (q2A w (f, b) (f, b)) := by sorry

end AdviceBonus
