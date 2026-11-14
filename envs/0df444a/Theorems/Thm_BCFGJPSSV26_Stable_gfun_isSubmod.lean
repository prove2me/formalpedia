-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_gfun_isSubmod
-- name    : BCFGJPSSV26.Stable.gfun_isSubmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:51.217089+00:00
-- url     : https://prove2.me/theorems/82beda8f-e0f4-4225-9458-fd0abf05b67f
-- title:
--   The function $g(\emptyset)-g$ of the submodular step is submodular (Part II, Section 5)
-- statement:
--   This is the submodularity statement behind the submodular step of Part II, Section 5: the gain $f=g(\emptyset)-g$ of the objective $g$ of that step is a submodular set function.
--
--   Let $I$ be a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$), and let $d(a,F)$ be the distance from a point $a$ to the nearest facility of $F$. A *dummy* $\lambda=(\ell,r)$ is a point $\ell$ (its leader, a client or a facility) with a real radius $r$; its distance to a point $a$ is $d(a,\lambda)=d(a,\ell)+r$, and its *ball* is the set of facilities within distance $r$ of $\ell$. For a set $F$ of facilities and a list $\Lambda$ of dummies, the *mixed set* $(F,\Lambda)$ has $d(a,(F,\Lambda))=\min\bigl(d(a,F),\min_{\lambda\in\Lambda}d(a,\lambda)\bigr)$ and $\mathrm{cost}(F,\Lambda)=\sum_j d(j,(F,\Lambda))$.
--
--   Let $LS'$ be a set of facilities, $\Lambda$ a list of dummies, *red* and *blue* two sets of facilities and $z$ a natural number. Write $M'=(LS',\Lambda)$; for a facility $c$, let $M_c$ be its cluster in $M'$: the clients whose nearest facility of $LS'$ is $c$ (ties to the least index) and that are at least as near to $LS'$ as to every dummy of $\Lambda$; and let $\mathrm{cost}_{M'}(E)=\sum_{j\in E}d(j,M')$. For a set $Y$ of facilities define
--
--   $$g_1(Y)=\sum_{j}\min\bigl(d(j,M'),\,d(j,Y)\bigr),\qquad h_c(Y)=\mathrm{cost}_{M'}(M_c)+|M_c|\cdot d\bigl(c,(\mathrm{blue}\cup Y,\Lambda)\bigr),$$
--
--   $$g_2(Y)=\min_{Z\subseteq\mathrm{red},\ |Z|=z}\ \sum_{c\in Z}h_c(Y),\qquad g(Y)=g_1(Y)+g_2(Y),$$
--
--   so that $g_2(Y)$ is the sum of the $z$ smallest values $h_c(Y)$ over red $c$.
--
--   **Statement.** The function $f(Y)=g(\emptyset)-g(Y)$ on finite sets of facilities is submodular: for all sets $A\subseteq B$ of facilities and every facility $e$,
--
--   $$f(B\cup\{e\})-f(B)\;\le\;f(A\cup\{e\})-f(A).$$
--
--   In the algorithm, $LS'$ and $\Lambda$ are the outcome of the samplings, red and blue a random coloring of $LS'$, and $z$ the number of centers to close; the candidate is $(LS'\setminus\hat Z)\cup\hat Y$, where $\hat Y$ approximately maximizes $f$ subject to containing one facility of each ball of $\Lambda$ and a guessed number of further facilities. Since $f$ is also monotone with $f(\emptyset)=0$, the sequential greedy applies and returns a $\hat Y$ gaining a $1-(1+1/N)^{-N}$ fraction of the gain of the comparison solution; this is the input of the bound on the candidate (Theorem 3.4).
--
--   **Formalization Note** The statement needs no relation between $LS'$, red and blue and no sign condition on the radii. The distance to an empty set (of facilities or of dummies) is a finite number larger than all distances, and $g_2(Y)=0$ when $z>|\mathrm{red}|$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 5. Lean source: `BCFGJPSSV26.Stable.gfun_isSubmod`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/Candidate.lean#L255-L262

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

theorem gfun_isSubmod (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (red blue : Finset (Fin I.m)) (z : ℕ) :
    IsSubmod fun Y ↦ gfun I LS' Λ red blue z ∅ - gfun I LS' Λ red blue z Y := by sorry

end BCFGJPSSV26.Stable
end
