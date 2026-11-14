-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_fl_arith
-- name    : BCFGJPSSV26.FL.fl_arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:55.135194+00:00
-- url     : https://prove2.me/theorems/dd449dbf-a16c-451e-8f54-3e8f8f150e8f
-- title:
--   Arithmetic of the LMP guarantee: the robust LMP bound scaled back to the original metric
-- statement:
--   This is the arithmetic step in the proof of Theorem 1.4 of Part I (arXiv:2610.18144): the robust LMP inequality for the rescaled instance implies the LMP inequality with factor $\lambda=1.9499$ for the original one.
--
--   **Constants.** $\lambda=1.9499$, $\delta=10^{-6}$ and $\rho=2-(1.224-1)^2=1.949824$.
--
--   **Statement.** Let $t, A, B, c_S, c_O, s, s', o, f, \hat f, d_{\min}, n$ be rational numbers such that
--
--   - $t>0$ and $f\ge0$;
--   - $\hat f=\lambda\,(1-\delta)\,f/t$;
--   - $c_S/t+n\le A$ and $B=c_O/t+n$;
--   - $s'\le s$;
--   - $n\,t\le d_{\min}/10^5$ and $0<d_{\min}\le c_O$;
--   - $(1-\delta)\,A+s\,\hat f\ \le\ (\rho+6\delta)\,B+o\,\hat f$.
--
--   Then
--
--   $$c_S+\lambda\,f\,s'\ \le\ \lambda\,\big(c_O+f\,o\big).$$
--
--   **Role.** It is applied to the greedy run of the facility-location algorithm: $t$ is the scale, the distances of the rescaled instance are $d/t+1$, so that a set of cost $c$ costs $c/t+n$ after rescaling; $c_S$ and $c_O$ are the costs of the greedy solution $S$ and of a comparison set $O$ with $|O|=o$; $A$ is the connection cost of the greedy solution and $B$ the cost of $O$ in the rescaled instance; $s$ is the number of regular atoms of the solution and $s'=|S|$; $\hat f$ is the scaled opening cost; $d_{\min}$ is the least positive client–facility distance. The last hypothesis is then the robust LMP guarantee (Part I, Theorem D.7) with slack $0$, and the conclusion is $\mathrm{cost}(S)+\lambda f|S|\le\lambda(\mathrm{cost}(O)+f|O|)$.
--
--   **Formalization Note** In Lean the right side of the last hypothesis carries the additional term $s\cdot n\cdot 0$, the slack term $s\,n\,\eta$ of the robust LMP guarantee at $\eta=0$. No sign condition is assumed on $n$, $s$, $s'$, $o$, $c_S$ or $A$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.FL.fl_arith`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Run.lean#L304-L336

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

theorem fl_arith {t A B cs co s sl o f fh dm n : ℚ} (ht : 0 < t) (hf : 0 ≤ f)
    (hfh : fh = lmpC * (1 - δ0) * f / t) (hA : cs / t + n ≤ A) (hB : B = co / t + n)
    (hsl : sl ≤ s) (hnt : n * t ≤ dm / cS) (hdm0 : 0 < dm) (hdm : dm ≤ co)
    (hlmp : (1 - δ0) * A + s * fh ≤ (ρ + 6 * δ0) * B + o * fh + s * n * 0) :
    cs + lmpC * f * sl ≤ lmpC * (co + f * o) := by sorry

end BCFGJPSSV26.FL
end
