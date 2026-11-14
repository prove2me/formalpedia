-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_rstar_nonneg
-- name    : BCFGJPSSV26.Greedy.Run.rstar_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:06.187645+00:00
-- url     : https://prove2.me/theorems/c4794208-1b14-4e22-8614-2d13da3f30dd
-- title:
--   The variables $r^\star$ of the embedding into the factor-revealing program are nonnegative
-- statement:
--   A feasibility fact for the embedding of the log-adaptive greedy algorithm into the factor-revealing program (Appendix E.4 of Part I): the variables $r^\star_{jk}$ built from an execution are nonnegative.
--
--   **Setting.** A *run* consists of a pseudometric space with rational distances on $n$ clients and $m$ facilities with all client–facility distances at least $1$; parameters $\delta,\varepsilon,\eta,K,R$ with $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta\ge0$, $n\eta\le\tfrac{\delta\varepsilon}{10}$ and $K\ge2\theta_R$, where $\theta_r=(1+\varepsilon^2)^r$; an opening cost $\hat f>n\eta$; and an $\eta$-valid solution $H$ for $\hat f$ (Definitions D.3 and D.6 of Part I, profiles capped at $K$). Its execution (Appendix E.1) is a list of atomic steps: the openings of the atoms of $H_0,H_1,\dots$ in order, and a raise of the time from $\theta$ to $(1+\varepsilon^2)\theta$ after each sequence of type 2. Step $s$ has a time $\theta_s$ and a profile $D_s$ of the atoms opened before it. For a client $j$, $\sigma(j)$ is the first step after which $j$ is inactive and $\alpha^*_j$ is its value at that moment (the paper's $\alpha^*_j$). Clients are ordered by $(\sigma(j),\alpha^*_j,j)$, lexicographically.
--
--   **The values $\zeta$.** The *witness* of a step $s$ is, for the opening of a regular facility in a sequence of type 2, a set of pairs (facility, offset $\ge0$) containing the open ones with respect to which the facility is $(2,\eta)$-openable, the open set itself whenever possible; for every other step it is the open set. Let $\tilde D_s$ be its profile. Then $\zeta_j(s)=(1-\delta)\tilde D_s(j)$ if $(1-\delta)\tilde D_s(j)\le\theta_s$; otherwise $\zeta_j(s)=\alpha^*_j$ if $\sigma(j)=s$, and $\zeta_j(s)=\theta_s$ if $\sigma(j)\ne s$ (the paper's $Z_{j,\cdot}$ and $\zeta_{j,\cdot}$).
--
--   **FREEZING** (Definition E.10 of Part I). Let $D_g$ be a nonempty set of clients with last client $k_\ell$, let $s_\ell=\sigma(k_\ell)$ and $\theta_\ell=\theta_{s_\ell}$, and let $i^\star$ be a facility. FREEZING holds for $(i^\star,D_g)$ if: step $s_\ell$ opens a regular facility $i_0^\star$ in a sequence of type 2; $\alpha^*_{k_\ell}>\theta_\ell$; $i_0^\star$ is not $(2,\eta)$-openable with respect to the profile $D_{s_\ell}$ of the open set itself; and $i^\star$ is a candidate before that step (Definition E.5): $\sum_j\beta\bigl(c_j,(1-\tfrac{\delta}{2})d(j,i^\star)\bigr)\ge\hat f-n\eta$, where $c_j=(1+\varepsilon^2)\theta_\ell$ if $\theta_\ell<(1-\delta)D_{s_\ell}(j)$ and $c_j=(1-\delta)D_{s_\ell}(j)$ otherwise, and $\beta(x,y)=\max(x-\tfrac{153}{125}y,0)$.
--
--   **The variables.** Let $D_g$ be a nonempty set of clients and $i^\star$ a facility, with $k_\ell$, $s_\ell$, $\theta_\ell$, $i_0^\star$ as above. For $j\in D_g$ and $k\in D_g\cup\{\top\}$, let $t(k)=\sigma(k)$ for $k\in D_g$ and let $t(\top)$ be the number of steps; put $r_{jk}=\alpha^*_j$ if $t(k)=\sigma(j)$ and $r_{jk}=(1-\delta)D_{t(k)}(j)$ otherwise, and $\zeta_{jk}=\zeta_j(\sigma(k))$ for $k\in D_g$. Let $k_f$ be the first client $k\in D_g$ with $\sigma(k)=s_\ell$ and $\alpha^*_k>\theta_\ell$ ($k_f=k_\ell$ if there is none). Then
--   $$r^\star_{jk}=\begin{cases}0&\text{if FREEZING holds and }k=\top,\\ \zeta_{jk}&\text{if FREEZING holds, }k_f\le k\ne\top\text{ and }d(j,i_0^\star)\le\theta_\ell/3,\\ \min\bigl(r_{jk},\max(\zeta_{jk},d(j,i^\star))\bigr)&\text{if FREEZING holds, }k_f\le k\ne\top\text{ and }d(j,i_0^\star)>\theta_\ell/3,\\ r_{jk}&\text{otherwise.}\end{cases}$$
--
--   **Statement.** Let $\rho=1.949824$ and assume $\rho\,d(j,i^\star)\le\alpha^*_j$ for every $j\in D_g$. Then for all $j\in D_g$ and $k\in D_g\cup\{\top\}$,
--
--   $$r^\star_{jk}\ \ge\ 0 .$$
--
--   The clients served by one facility $i^\star$ of a competing solution, with the variables $r^\star$, the distances $d(j,i^\star)$ and $\hat f$, form a feasible point of the factor-revealing program (Lemmas E.13 to E.16 of Part I). Nonnegativity is one of the conditions of that program, and its bound $\rho$ then gives the robust LMP guarantee (Theorem D.7).
--
--   **Formalization Note** The hypothesis $\rho\,d(j,i^\star)\le\alpha^*_j$ is a standing assumption of this part of the formalization and is part of the formal statement. Openability of type 2 is restricted to the one-parameter family of bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Appendix E.4. Lean source: `BCFGJPSSV26.Greedy.Run.rstar_nonneg`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Embed.lean#L710-L721

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

set_option linter.unusedSectionVars false in

theorem rstar_nonneg (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : 0 ≤ R.rstar hne istar j k := by sorry

end Run
end BCFGJPSSV26.Greedy
end
