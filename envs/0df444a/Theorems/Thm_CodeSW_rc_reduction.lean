-- Prove2me | Theorems.Thm_CodeSW_rc_reduction
-- name    : CodeSW.rc_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:31.775208+00:00
-- url     : https://prove2.me/theorems/9d2bc9cb-074f-4229-a6ab-4ee40a0b2dbd
-- title:
--   §3.3.1, p.17 — reduction to the RC model: $d_{\mathrm{CSW}}(t+1)\le d_{\mathrm{SW}}(t)$
-- statement:
--   **Reduction to the random cluster model.** Let $\beta>0$ and $p=1-e^{-2\beta}$. Write $d_{\mathrm{CSW}}(t)=\max_x\|P^t(x,\cdot)-\pi\|_{\mathrm{TV}}$ for the Code Swendsen-Wang chain $P$ with its Gibbs distribution $\pi$, and $d_{\mathrm{SW}}(t)=\max_B\|P_{\mathrm{SW}}^t(B,\cdot)-\phi\|_{\mathrm{TV}}$ for the Swendsen-Wang chain of the random cluster model. Then for every $t\ge0$,
--   $$d_{\mathrm{CSW}}(t+1)\le d_{\mathrm{SW}}(t).$$
--   In particular $\tau(P)\le\tau(P_{\mathrm{SW}})+1$. This lets every mixing bound be proved on the state space of subsets of checks.
--
--   Differences from the source:
--   - reading: 'it is sufficient to prove a mixing time bound for the convergence to the RC model' (an unnumbered sentence) → d_CSW(t+1) ≤ d_SW(t) for every t; reason: this is the precise content the argument needs, and it gives the reduction at every accuracy
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.3.1, p.17

import Definitions.Def_CodeSW_cswKernel
import Definitions.Def_CodeSW_rc
import Definitions.Def_mm_mixing
open Matrix

namespace CodeSW

/-- **§3.3.1 reduction to the random cluster model.** "To prove mixing times of the SW algorithm
for the Gibbs distribution, it is sufficient to prove a mixing time bound for the convergence to
the RC model instead": for `β > 0` and `p = 1 − e^{−2β}`, the distance of the Code SW chain from
`π` after `t + 1` steps is at most the distance of the RC Swendsen-Wang chain `P_SW` from `ϕ`
after `t` steps, so `τ(P_CSW) ≤ τ(P_SW) + 1`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.3.1, p.17).

**Formalization Note** `d(t) = max_x ‖P^t(x,·) − π‖_TV` is `MarkovMixing.distStationary`. The
unnumbered sentence is read as this comparison of distances, which gives the mixing-time
reduction at every accuracy. -/
theorem rc_reduction {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (β : ℝ) (hβ : 0 < β)
    (t : ℕ) :
    MarkovMixing.distStationary (cswKernel h β) (gibbs h β) (t + 1) ≤
      MarkovMixing.distStationary (swRC h (bondProb β)) (rc h (bondProb β)) t := by sorry

end CodeSW
