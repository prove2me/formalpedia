-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_Zv_ge_third
-- name    : BCFGJPSSV26.Greedy.Run.Zv_ge_third
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:33.745799+00:00
-- url     : https://prove2.me/theorems/e98fa5c0-46eb-4e1a-bcee-33d344fc4504
-- title:
--   Under FREEZING, a client near the opened facility has $\zeta\ge\theta/3$ (a consequence of Lemma E.11, Part I)
-- statement:
--   A consequence of Lemma E.11 of Part I, used in the embedding into the factor-revealing program (Appendix E.4): under the event FREEZING, every client of the group that is close to the facility opened at the last step has $\zeta$-value at least a third of the time.
--
--   **Setting.** A *run* consists of a pseudometric space with rational distances on $n$ clients and $m$ facilities with all client–facility distances at least $1$; parameters $\delta,\varepsilon,\eta,K,R$ with $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta\ge0$, $n\eta\le\tfrac{\delta\varepsilon}{10}$ and $K\ge2\theta_R$, where $\theta_r=(1+\varepsilon^2)^r$; an opening cost $\hat f>n\eta$; and an $\eta$-valid solution $H$ for $\hat f$ (Definitions D.3 and D.6 of Part I, profiles capped at $K$). Its execution (Appendix E.1) is a list of atomic steps: the openings of the atoms of $H_0,H_1,\dots$ in order, and a raise of the time from $\theta$ to $(1+\varepsilon^2)\theta$ after each sequence of type 2. Step $s$ has a time $\theta_s$ and a profile $D_s$ of the atoms opened before it. For a client $j$, $\sigma(j)$ is the first step after which $j$ is inactive and $\alpha^*_j$ is its value at that moment (the paper's $\alpha^*_j$). Clients are ordered by $(\sigma(j),\alpha^*_j,j)$, lexicographically.
--
--   **The values $\zeta$.** The *witness* of a step $s$ is, for the opening of a regular facility in a sequence of type 2, a set of pairs (facility, offset $\ge0$) containing the open ones with respect to which the facility is $(2,\eta)$-openable, the open set itself whenever possible; for every other step it is the open set. Let $\tilde D_s$ be its profile. Then $\zeta_j(s)=(1-\delta)\tilde D_s(j)$ if $(1-\delta)\tilde D_s(j)\le\theta_s$; otherwise $\zeta_j(s)=\alpha^*_j$ if $\sigma(j)=s$, and $\zeta_j(s)=\theta_s$ if $\sigma(j)\ne s$ (the paper's $Z_{j,\cdot}$ and $\zeta_{j,\cdot}$).
--
--   **FREEZING** (Definition E.10 of Part I). Let $D_g$ be a nonempty set of clients with last client $k_\ell$, let $s_\ell=\sigma(k_\ell)$ and $\theta_\ell=\theta_{s_\ell}$, and let $i^\star$ be a facility. FREEZING holds for $(i^\star,D_g)$ if: step $s_\ell$ opens a regular facility $i_0^\star$ in a sequence of type 2; $\alpha^*_{k_\ell}>\theta_\ell$; $i_0^\star$ is not $(2,\eta)$-openable with respect to the profile $D_{s_\ell}$ of the open set itself; and $i^\star$ is a candidate before that step (Definition E.5): $\sum_j\beta\bigl(c_j,(1-\tfrac{\delta}{2})d(j,i^\star)\bigr)\ge\hat f-n\eta$, where $c_j=(1+\varepsilon^2)\theta_\ell$ if $\theta_\ell<(1-\delta)D_{s_\ell}(j)$ and $c_j=(1-\delta)D_{s_\ell}(j)$ otherwise, and $\beta(x,y)=\max(x-\tfrac{153}{125}y,0)$.
--
--   **Statement.** Assume FREEZING holds for $(i^\star,D_g)$. Then every client $j\in D_g$ with $d(j,i_0^\star)\le\theta_\ell/3$ satisfies
--
--   $$\zeta_j(s_\ell)\ \ge\ \frac{\theta_\ell}{3}.$$
--
--   Under FREEZING the variables $r^\star_{jk}$ of the factor-revealing program are set to $\zeta_j(s_\ell)$ for the clients $j$ within $\theta_\ell/3$ of $i_0^\star$. The bound shows that these variables are nonnegative, as the feasibility of the embedding requires (Lemmas E.13 to E.16 of Part I), and it is used again in the cost bounds that give the robust LMP guarantee (Theorem D.7).
--
--   **Formalization Note** Openability of type 2 is restricted to the one-parameter family of bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$. Everything is indexed by steps of the execution, which replaces the paper's indexing by clients and open sets.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemma E.11 and Definition E.10. Lean source: `BCFGJPSSV26.Greedy.Run.Zv_ge_third`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Embed.lean#L583-L622

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

theorem Zv_ge_third (hF : R.Freezing hne istar) (j : R.DgT Dg)
    (hj : R.X.d j.val (R.opened (R.σ (R.kl hne).val) istar) ≤ R.θl hne / 3) :
    R.θl hne / 3 ≤ R.Zv j.val (R.σ (R.kl hne).val) := by sorry

end
end Run
end BCFGJPSSV26.Greedy
end
