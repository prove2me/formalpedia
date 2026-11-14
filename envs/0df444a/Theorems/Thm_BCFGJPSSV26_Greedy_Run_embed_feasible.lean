-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_embed_feasible
-- name    : BCFGJPSSV26.Greedy.Run.embed_feasible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:20.746709+00:00
-- url     : https://prove2.me/theorems/ba3e24c7-308d-43b0-8003-328a3748f6e1
-- title:
--   Feasibility of the embedding of the greedy execution into the factor-revealing program
-- statement:
--   This is the embedding of [Part I, Appendix E.4] (Lemmas E.13 to E.16): the clients charged to one facility $i^\star$ give a point that satisfies every constraint of the factor-revealing program of [Part I, Definition 4.1] except the normalization.
--
--   **Setting.** A *run* consists of a pseudometric with rational values on $n$ clients and $m$ facilities with $d(j,i)\ge 1$ for every client $j$ and facility $i$; parameters $(\delta,\varepsilon,\eta,K,R)$ with $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta\ge 0$, $n\,\eta\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$; an opening cost $f>n\eta$; and an $\eta$-valid solution $H=(H_0,\dots,H_{2R-1})$ for $f$ ([Part I, Definitions D.3 and D.6]): $2R$ valid and maximal sequences of atoms (regular facilities, or free copies of a facility at an offset $u\in[0,K]$), of type 1 for even and type 2 for odd index, after which every client is inactive. The *execution* is the list of steps that opens the atoms of $H_0,H_1,\dots$ in order and, after each sequence of type 2, has one step that raises the time from $\theta$ to $(1+\varepsilon^2)\theta$. A step $s$ of sequence $p$ has time $\theta_s=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$ and sees the profile $D_s(j)=\min\big(K,\min_{(i,u)}(d(j,i)+u)\big)$, the minimum being over the atoms (facility $i$, offset $u$) opened before step $s$. The bid is $\beta(x,y)=\max(x-\gamma y,0)$ with $\gamma=\frac{153}{125}$. Let $\theta_s^+$ be the time after step $s$, that is $(1+\varepsilon^2)\theta_s$ if step $s$ raises the time and $\theta_s$ otherwise, and let $\rho=2-(\gamma-1)^2=1.949824$.
--
--   **Quantities of the execution.**
--
--   - $\sigma(j)$ is the first step $s$ after which client $j$ is inactive, i.e. $(1-\delta)D_{s+1}(j)\le\theta_s^+$.
--   - If step $s$ opens a regular facility $i$ in a sequence of type 2, a witness $(\tilde S_s,T_s)$ of its $(2,\eta)$-openability is fixed (a set of pairs containing those opened before $s$, taken equal to it whenever possible, and $T_s\in[\theta_s,(1+\varepsilon^2)\theta_s]$); $\tilde D_s$ is the profile of $\tilde S_s$ and $\tau_j=\min\big((1-\delta)\tilde D_s(j),g_j\big)$, with $g_j=\max\big(\theta_s,\min(T_s,(1+\varepsilon)\theta_s-d(j,i))\big)$ if $d(j,i)\le\varepsilon\theta_s$ and $g_j=\theta_s$ otherwise; being a witness means that $\sum_j\beta\big(\tau_j,(1-\frac{\delta}{2})d(j,i)\big)\ge f-n\eta$ and $\sum_j\beta\big(\tau_j,d(j,i_0)\big)\le f$ for every facility $i_0$. For every other step, $\tilde D_s=D_s$.
--   - $\alpha^{\ast}_j$, for $s=\sigma(j)$: it is $(1-\delta)D_s(j)$ if $s$ raises the time; it is $\tau_j$ if $s$ opens a regular facility in a sequence of type 2 and $\theta_s<(1-\delta)\tilde D_s(j)$; it is $\theta_s$ otherwise.
--   - $R_{j,s}=\alpha^{\ast}_j$ if $s=\sigma(j)$ and $R_{j,s}=(1-\delta)D_s(j)$ otherwise (at the end of the execution, $D_s$ is the final profile).
--   - $Z_{j,s}=(1-\delta)\tilde D_s(j)$ if $\theta_s\ge(1-\delta)\tilde D_s(j)$; otherwise $Z_{j,s}=\alpha^{\ast}_j$ if $\sigma(j)=s$ and $Z_{j,s}=\theta_s$ if not.
--
--   **The embedding.** Let $i^\star$ be a facility and $D_g$ a nonempty set of clients with $\rho\,d(j,i^\star)\le\alpha^{\ast}_j$ for all $j\in D_g$. Order $D_g$ lexicographically by $(\sigma(j),\alpha^{\ast}_j,j)$, and add a last time $\top$. For a time $t$ let $s(t)=\sigma(t)$ if $t\in D_g$, and let $s(\top)$ be the end of the execution; put $r_{jt}=R_{j,s(t)}$, and $\zeta_{jk}=Z_{j,\sigma(k)}$ for $k\in D_g$. Let $k_\ell$ be the last client of $D_g$ and $\theta_\ell=\theta_{\sigma(k_\ell)}$. The event FREEZING ([Part I, Definition E.10]) holds if step $\sigma(k_\ell)$ opens a regular facility $i_0^\star$ in a sequence of type 2, $\alpha^{\ast}_{k_\ell}>\theta_\ell$, the set of pairs opened before that step is not, with any $T$, a witness for $i_0^\star$, and $i^\star$ is a candidate before that step: $\sum_j\beta\big(c_j,(1-\frac{\delta}{2})d(j,i^\star)\big)\ge f-n\eta$, where $c_j=(1+\varepsilon^2)\theta_\ell$ if $\theta_\ell<(1-\delta)D_{\sigma(k_\ell)}(j)$ and $c_j=(1-\delta)D_{\sigma(k_\ell)}(j)$ otherwise. Let $k_f$ be the first $k\in D_g$ with $\sigma(k)=\sigma(k_\ell)$ and $\alpha^{\ast}_k>\theta_\ell$ (under FREEZING, $k_\ell$ is such a client). Define $r^\star_{jt}=r_{jt}$ for all clients $j\in D_g$ and times $t$, except that under FREEZING $r^\star_{j\top}=0$ and, for $k\in D_g$ with $k\succeq k_f$,
--
--   $$r^\star_{jk}=\begin{cases}\zeta_{jk}&\text{if }d(j,i_0^\star)\le\theta_\ell/3,\\ \min\big(r_{jk},\max(\zeta_{jk},d(j,i^\star))\big)&\text{otherwise.}\end{cases}$$
--
--   **Statement.** With $d_j=d(j,i^\star)$ and $k^+$ the successor of $k$ in $D_g$ ($\top$ for the last client), for all $j,k,l\in D_g$:
--
--   1. $r^\star_{j,k^+}\le r^\star_{jk}$ whenever $j\preceq k$;
--   2. $r^\star_{kk}\le r^\star_{jk}+d_k+d_j$ whenever $j\prec k$;
--   3. $r^\star_{jt}\le r^\star_{lt}+d_l+d_j$ for every time $t\in D_g\cup\{\top\}$ with $j\prec t$ and $l\prec t$;
--   4. the facility constraint holds for every $k$:
--
--   $$\sum_{j\prec k}\beta\big(r^\star_{jk},d_j\big)+\sum_{j\succeq k}\beta\big(r^\star_{kk},d_j\big)\le f;$$
--
--   5. $f\ge 0$, $d_j\ge 0$ and $r^\star_{jt}\ge 0$ for all $j$ and all times $t$.
--
--   Together with the bound $f+\rho\sum_j d_j$ on the factor-revealing program, this bounds what the clients of $D_g$ pay ([Part I, Lemma E.17]); summing over the facilities of a comparison solution gives the robust LMP guarantee ([Part I, Theorem D.7]) behind Theorems 1.2 and 1.4.
--
--   **Formalization Note** All quantities are rational and indexed by the steps of the execution, which replaces the paper's indexings by clients and by open sets. The normalization $\sum_j d_j=1$ is not part of the statement. Type-2 openability is the restricted one, with the one-parameter bids above.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Appendix E.4, Lemmas E.13–E.16. Lean source: `BCFGJPSSV26.Greedy.Run.embed_feasible`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Embed.lean#L987-L1001

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP
public import Definitions.Def_BCFGJPSSV26_Greedy_Embed

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Embed

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

end Embed

namespace Run

variable {n m : ℕ} (R : Run n m)

variable (Dg : Finset (Fin n))

variable {Dg}

variable (hne : Dg.Nonempty)
include hne

section

variable {istar : Fin m}

end

variable {istar : Fin m} (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j)
include hD

theorem embed_feasible :
    FRP.FeasibleOn (R.rstar hne istar) (fun j ↦ R.X.d j.val istar) R.f := by sorry

end Run
end BCFGJPSSV26.Greedy
end
