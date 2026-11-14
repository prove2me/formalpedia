-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_robust_lmp
-- name    : BCFGJPSSV26.Greedy.robust_lmp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:34.398898+00:00
-- url     : https://prove2.me/theorems/c3f7c93a-c059-47a5-ac8c-c9b34ab9c6f9
-- title:
--   Theorem D.7 (Part I) — robust LMP guarantee of the log-adaptive greedy, in linear form
-- statement:
--   This is the robust LMP guarantee of [Part I, Theorem D.7], in linear form: every $\eta$-valid solution of the log-adaptive greedy pays for its regular facilities and its connection cost against any nonempty set of facilities, with factor $\rho+6\delta$ on the connection cost of that set.
--
--   **Setting.** Consider a pseudometric with rational values on $n$ clients and $m$ facilities such that $d(j,i)\ge 1$ for every client $j$ and facility $i$, and parameters $(\delta,\varepsilon,\eta,K,R)$ with $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta\ge 0$, $n\,\eta\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,0)$, $\gamma=\frac{153}{125}$, and $\rho=2-(\gamma-1)^2=1.949824$. For a time $\theta$ and a profile $D$, client $j$ has value $v_j=\min(\theta,(1-\delta)D_j)$; for a facility $i$ and $T$ it bids $\tau_j^{i,T}=\min\big((1-\delta)D_j,g_j\big)$, where $g_j=\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)$ if $d(j,i)\le\varepsilon\theta$ and $g_j=\theta$ otherwise. For an opening cost $f$, facility $i$ is $(1,\eta')$-openable if $\sum_j\beta\big(v_j,(1-\delta)d(j,i)\big)\ge f-n\eta'$, and $(2,\eta')$-openable if for some $T\in[\theta,(1+\varepsilon^2)\theta]$ one has $\sum_j\beta\big(\tau_j^{i,T},(1-\frac{\delta}{2})d(j,i)\big)\ge f-n\eta'$ and $\sum_j\beta\big(\tau_j^{i,T},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   Let $f>n\eta$ and let $H=(H_0,\dots,H_{2R-1})$ be an *$\eta$-valid solution* for $f$: exactly $2R$ sequences of atoms, where
--
--   - every atom is a regular facility (offset $0$) or a free copy of a facility at an offset $u\in[0,K]$, and the profile of a set $L$ of pairs is $D_L(j)=\min\big(K,\min_{(i,u)\in L}(d(j,i)+u)\big)$;
--   - sequence $p$ has type $\nu_p=1$ for even $p$ and $\nu_p=2$ for odd $p$, and time $\theta_p=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$; each atom of $H_p$ is a free copy, or its facility is $(\nu_p,\eta)$-openable at time $\theta_p$ for the profile of some finite set of pairs with nonnegative offsets containing all atoms before it;
--   - after $H_p$, no facility is $(\nu_p,0)$-openable at time $\theta_p$ for the profile of the atoms of $H_0,\dots,H_p$;
--   - at the end every client is inactive: $(1-\delta)D_H(j)\le(1+\varepsilon^2)^R$, where $D_H$ is the profile of all atoms of $H$.
--
--   **Statement.** For every nonempty set $O$ of facilities,
--
--   $$(1-\delta)\sum_{j}D_H(j)\;+\;\lvert H_{\mathrm{reg}}\rvert\,f\;\le\;(\rho+6\delta)\,\mathrm{cost}(O)\;+\;\lvert O\rvert\,f\;+\;\lvert H_{\mathrm{reg}}\rvert\,n\,\eta,$$
--
--   where $\lvert H_{\mathrm{reg}}\rvert$ is the number of regular atoms of $H$ and $\mathrm{cost}(O)=\sum_j\min_{i\in O}d(j,i)$.
--
--   This is the guarantee of the greedy solutions on which both applications rest: for Theorem 1.2 it is applied, with $O$ an optimal set of at most $k$ facilities, to the solution produced by the bisection on $f$ and the merge, and for Theorem 1.4 (facility location) to a single greedy run with $\eta=0$.
--
--   **Formalization Note** The paper states the bound as a ratio against $\mathrm{OPT}-\lvert S_{\mathrm{reg}}\rvert f$, which may be negative by up to $\lvert S_{\mathrm{reg}}\rvert n\eta$; the linear form avoids the division. Type-2 openability is restricted to the one-parameter family of bids above, which implies the paper's [Part I, Definition D.2]. All quantities are rational.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem D.7. Lean source: `BCFGJPSSV26.Greedy.robust_lmp`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/LMP.lean#L324-L330

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Embed
public import Definitions.Def_BCFGJPSSV26_Greedy_LMP

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

end Run

theorem robust_lmp {n m : ℕ} (X : Space n m) (P : Par) (hP : P.Good n) (hd1 : ∀ j i, 1 ≤ X.d j i)
    {f : ℚ} (hf : n * P.η < f) {H : List (List (Atom m))} (hH : Sol P X.d f P.η H)
    (O : Finset (Fin m)) (hO : O.Nonempty) :
    (1 - P.δ) * connCost P X.d H + nReg H * f ≤
      (ρ + 6 * P.δ) * costF X.d O + O.card * f + nReg H * n * P.η := by sorry

end BCFGJPSSV26.Greedy
end
