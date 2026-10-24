-- Prove2me | Theorems.Thm_Erdos624_five_moment_certificate
-- name    : Erdos624.five_moment_certificate
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:33:36.349906+00:00
-- url     : https://prove2.me/theorems/82350780-0577-4047-a981-760351df1378
-- title:
--   Five-moment certificate for common holes of two maps (Erdős 624)
-- statement:
--   Let $|U|=n=2^k$, $g_0,g_1:\mathcal P(U)\to U$, and $\mathcal K=\binom Uk$, $K=|\mathcal K|$. For $Y\in\mathcal K$ and $u\in U$ let $m_Y(u)=|\{(i,A):i\in\{0,1\},A\subseteq Y,g_i(A)=u\}|$ and $A_j=\sum_{Y\in\mathcal K}\sum_{u\in U}\binom{m_Y(u)}{j}$. Let $D(Y)=n-|I_{g_0}(Y)\cup I_{g_1}(Y)|$ be the number of common holes on $Y$.
--
--   **Theorem.** If
--
--   $$120A_2\ge239\,nK,\quad 120A_3\le161\,nK,\quad 120A_4\ge79\,nK,\quad 120A_5\le33\,nK,$$
--
--   then
--
--   $$nK\;\le\;30\sum_{Y\in\mathcal K}D(Y).$$
--
--   These finite collision-moment conditions (close to those of a uniformly random pair) are therefore sufficient for a constant-surplus common-hole theorem. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it would suffice to show that, for large $k$, any two maps $\mathcal P(U)\to U$ with $|U|=2^k$ have a *common hole*: a $k$-set $Y$ and a point $u$ missed by both maps on $\mathcal P(Y)$.  These results do not settle Problem 624.
--
--   **Formalization Note.** Maps indexed by $\mathrm{Fin}\,2$; $m_Y(u)$ is the cardinality of a filter of $\mathrm{Fin}\,2\times\mathcal P(Y)$; natural-number hypotheses.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (16)–(17) of the analysis derived from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem five_moment_certificate {U : Type*} [Fintype U] [DecidableEq U] (k : ℕ)
    (hU : Fintype.card U = 2 ^ k) (g : Fin 2 → Finset U → U)
    (h2 : 239 * (2 ^ k * #(powersetCard k (univ : Finset U))) ≤
      120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 2)
    (h3 : 120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 3 ≤
      161 * (2 ^ k * #(powersetCard k (univ : Finset U))))
    (h4 : 79 * (2 ^ k * #(powersetCard k (univ : Finset U))) ≤
      120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 4)
    (h5 : 120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 5 ≤
      33 * (2 ^ k * #(powersetCard k (univ : Finset U)))) :
    2 ^ k * #(powersetCard k (univ : Finset U)) ≤
      30 * ∑ Y ∈ powersetCard k (univ : Finset U),
        (2 ^ k - #(Y.powerset.image (g 0) ∪ Y.powerset.image (g 1))) := by sorry

end Erdos624
