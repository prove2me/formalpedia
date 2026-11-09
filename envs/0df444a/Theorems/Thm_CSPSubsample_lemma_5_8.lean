-- Prove2me | Theorems.Thm_CSPSubsample_lemma_5_8
-- name    : CSPSubsample.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:11.757071+00:00
-- url     : https://prove2.me/theorems/957c0cef-226b-4c05-9e77-9e91a4d820f0
-- title:
--   Lemma 5.8 — swapping one variable changes $\mathrm{OPT}^{\mathrm{bal}}_\Phi$ by at most $k/N$
-- statement:
--   Let $\Phi\subseteq[q]^n$ be a nonempty family of assignments and $U,U'\subseteq[n]$ subsets of size $N$ with $|U\,\triangle\,U'|=2$. Then
--   $$
--   \big|\mathrm{OPT}^{\mathrm{bal}}_\Phi(U)-\mathrm{OPT}^{\mathrm{bal}}_\Phi(U')\big|\le\frac kN .
--   $$
--   This bounded-differences property is what moves the guarantee of Lemma 5.6 from the block-conditioned law to the uniform law $\mu$ on $N$-subsets.
--
--   Differences from the source:
--   - generalization: blocks V_1, …, V_T of size approximately n/T → an arbitrary block map b : [n] → [T]; reason: the statement holds for every partition of [n] into T blocks; it specializes to the paper's blocks
--   - encoding: Φ ⊆ [q]^n → Φ nonempty; reason: the maximum over the empty family is undefined
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 5.8, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valbal

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 5.8** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.18 = PDF p.20). Let `Φ ⊆ [q]^n` and
let `U, U' ⊆ [n]` be subsets of size `N` with `|U △ U'| = 2`. Then
`|OPT^bal_Φ(U) − OPT^bal_Φ(U')| ≤ k/N`.

**Formalization Note** Every block map `b`. `Φ` is assumed nonempty, since the maximum over the
empty family is undefined. -/
theorem lemma_5_8 {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (Φ : Finset (Fin n → Fin q)) (hΦ : Φ.Nonempty) (N : ℕ) (U U' : Finset (Fin n))
    (hU : U.card = N) (hU' : U'.card = N) (hUU' : (symmDiff U U').card = 2) :
    |OPTbalPhi I b Φ U - OPTbalPhi I b Φ U'| ≤ (k : ℝ) / N := by sorry

end CSPSubsample
