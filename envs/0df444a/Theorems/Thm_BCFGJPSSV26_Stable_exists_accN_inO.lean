-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_exists_accN_inO
-- name    : BCFGJPSSV26.Stable.exists_accN_inO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:50:21.367652+00:00
-- url     : https://prove2.me/theorems/94aebb93-f092-43a6-ac3f-f230d31f9b0d
-- title:
--   Computing the accuracy parameter $N$ from $\varepsilon$ in linear time plus $\mathrm{poly}(N)$
-- statement:
--   This is the first step of the running-time analysis of the algorithm for stable instances (Theorem 1.1 of Part II): the internal accuracy parameter $N=N(\varepsilon)$ is computable from the rational accuracy $\varepsilon$ in time linear in the encoding of $\varepsilon$ plus a polynomial in $N$.
--
--   For a rational number $\varepsilon=p/q$ in lowest terms with $q\ge1$, let $\mathrm{size}(x)$ denote the number of binary digits of a natural number $x$ ($\mathrm{size}(0)=0$), and define
--
--   $$N(\varepsilon)=2^{\,g+8},\qquad g=\begin{cases}\max\bigl(0,\ \mathrm{size}(q)-\mathrm{size}(p)-1\bigr), & p\ge0,\\ 0, & p<0.\end{cases}$$
--
--   **Statement.** There is a natural number $D$ such that the function $\varepsilon\mapsto N(\varepsilon)$, with $\varepsilon$ given in binary (the sign and the binary digits of $p$, then the binary digits of $q$) and the output written in unary, is computed by a deterministic multitape Turing machine that, for a constant $c$ and every $\varepsilon\in\mathbb{Q}$, halts within
--
--   $$c\,\bigl(|\mathrm{enc}(\varepsilon)|+N(\varepsilon)^{D}+1\bigr)$$
--
--   steps and uses at most that many tape cells.
--
--   The number $N(\varepsilon)$ satisfies $N\ge256$, $1/N<\varepsilon$ for $\varepsilon>0$, and $N\le256\,(\lceil1/\varepsilon\rceil+1)$. The algorithm of the main theorem first computes $N$ and then runs the algorithm for accuracy $1/N$, whose running time is bounded for $N$ given in unary. The encoding of $\varepsilon$ can be long while $1/\varepsilon$ is small, and the time bound of the main theorem allows only linear time in the length of the input beyond $2^{eL}(|I|+2)^e$; this is why $N$ is defined from the numbers of digits only, which needs no division.
--
--   **Formalization Note** The time and space bounds hold up to the constant $c$, as in the complexity library's notion of computability within $O(T)$ time and $O(S)$ space, which also bounds the length of the encoded output by the space bound.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Stable.exists_accN_inO`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/Accuracy.lean#L232-L312

module

public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_BuhaiPapers_Background_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM
open Encoding (encRat)

theorem exists_accN_inO : ∃ D : ℕ, ComputableInO accN encRat encUnary
    (fun ε ↦ (encRat ε).length + accN ε ^ D) (fun ε ↦ (encRat ε).length + accN ε ^ D) := by sorry

end BCFGJPSSV26.Stable
end
