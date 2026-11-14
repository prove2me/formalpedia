-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_algFor_polytime
-- name    : BCFGJPSSV26.Greedy.algFor_polytime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:54.925028+00:00
-- url     : https://prove2.me/theorems/23e3c37b-18fc-4899-a5ac-1fe5988d1769
-- title:
--   The algorithm of Theorem 1.2 for accuracy $\varepsilon$ runs in polynomial time
-- statement:
--   This is the running-time part of Theorem 1.2 of Part I: for every real $\varepsilon$, the algorithm $A_\varepsilon$ of the formalization is computable in polynomial time as a function of the k-median instance.
--
--   **The algorithm.** A k-median instance $I$ has $n$ clients, $m$ facilities, a number $k$ and rational distances between its $n+m$ points. The *trivial solution* $T$ is the list of the nearest facilities of the clients (least index on ties), without repetitions. $A_\varepsilon(I)$ is defined as follows.
--
--   - If $\varepsilon\ge 4$: output $[0]$ if $T$ is empty; output $T$ if it has at most $k$ facilities; otherwise output the result of the local search of Part II with swaps of size $24\cdot 201$, run with a budget of steps polynomial in the length of the encoding.
--   - If $\varepsilon<4$: take constants $(\delta,\varepsilon_g,\varepsilon')$, namely $(\delta,\frac{\delta}{10},25\delta)$ with a fixed rational $\delta\in(\frac{\varepsilon}{200},\frac{\varepsilon}{100})$ when $0<\varepsilon\le 1$, and $(\frac{1}{100},\frac{1}{1000},\frac{1}{4})$ otherwise. Output $[0]$ if $T$ is empty; output $T$ if it has at most $k+\lfloor\log_2 n\rfloor\lceil 1/\delta^2\rceil$ facilities. Otherwise, for every positive client–facility distance $\Lambda$ (a guess of the scale), run the core (greedy solutions, bisection on the opening cost, merge) on the distances $\min(d/t+1,\,M)$ with $t=\varepsilon'\Lambda/n$ and $M=8n^2/\varepsilon'+1$; among the outputs that are lists of at most $k+6R$ distinct facilities, where $R=\lceil 1/\varepsilon_g^2\rceil\lceil\log_2\lceil 5nM\rceil\rceil+1$, output one of least exact cost for the original distances ($[0]$ if there is none).
--
--   **Statement.** For every $\varepsilon\in\mathbb{R}$ there are polynomially bounded functions $t,s$ and a deterministic multitape Turing machine that, on the encoding $\langle I\rangle$ of any instance $I$, outputs the encoding of $A_\varepsilon(I)$ within
--
--   $$t(\lvert\langle I\rangle\rvert)\ \text{steps}\quad\text{and}\quad s(\lvert\langle I\rangle\rvert)\ \text{cells}.$$
--
--   No condition is put on $\varepsilon$ (it may be nonpositive) or on $I$ (it need not be valid).
--
--   Together with the guarantee of $A_\varepsilon$ on valid instances (at most $k+10^{10}\ln n/\varepsilon^2$ distinct facilities of cost at most $(1.9499+\varepsilon)\,\mathrm{opt}_k$, for $\varepsilon>0$), this proves Theorem 1.2.
--
--   **Formalization Note** An instance is encoded by $n$, $m$, $k$ in binary and its $(n+m)\times(n+m)$ table of rational distances; the output is a list of facility indices in binary. The machine has a binary alphabet and finitely many states, and its time and space are bounded in terms of the length of the encoded input. The machine depends on $\varepsilon$, which is not part of the input.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.2 (running time). Lean source: `BCFGJPSSV26.Greedy.algFor_polytime`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/Main.lean#L199-L205

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

theorem algFor_polytime (ε : ℝ) :
    ComputableInPolyTime (fun I ↦ algFor ε (toRaw I)) encInstance encCenters := by sorry

end BCFGJPSSV26.Greedy
end
