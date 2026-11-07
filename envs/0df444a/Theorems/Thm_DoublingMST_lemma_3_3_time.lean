-- Prove2me | Theorems.Thm_DoublingMST_lemma_3_3_time
-- name    : DoublingMST.lemma_3_3_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:28.185439+00:00
-- url     : https://prove2.me/theorems/4f22eefe-0cff-472d-be2d-4f2a0fbe098c
-- title:
--   Lemma 3.3, running-time clauses — Algorithm 1 and $\Phi$ in $t^{O(\mathrm{ddim})}nL$ steps (clauses (1)–(5): lemma_3_3)
-- statement:
--   There are a program $P$ of the real RAM of Definition 2.1 and an absolute constant $C>0$ such that the following holds for every $n\ge2$, every injective labelling $\iota$ of the points by integers, every metric $d$ with minimum interpoint distance $>1$, every net hierarchy $N$ over $X$ and every $t\ge32$. Started on an integer memory holding the labels and $N$, with $t$ in a real register and distance oracle $d$, the program halts within
--
--   $$t^{C\operatorname{ddim}(X)}\,n\,L,\qquad L=\lceil\log_2\Delta\rceil+4,$$
--
--   steps, and at that point the integer memory holds:
--
--   1. the pairs of a collection $\Psi$ that is an output of Algorithm 1 on $N$ with parameter $t$;
--   2. for each $(u,v)\in\Psi$, explicit lists of the balls $B(u,2^{\mathrm{lev}(u)})$ and $B(v,2^{\mathrm{lev}(v)})$ of the cover $\Phi$.
--
--   These are the running-time clauses of Lemma 3.3; its properties (1)–(5) are the companion item `DoublingMST.lemma_3_3`, which holds for every output of Algorithm 1 and so for this one.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: minimum interpoint distance greater than 1 → hypothesis MinDistGtOne d; reason: a hypothesis of the printed lemma
--   - encoding: ddim(X) ≤ ddim → ddim(X) itself; reason: t^{C·D} is monotone in D, so the two are equivalent
--   - reading: t^{O(ddim)} → ∃ C > 0, chosen before the input and before t, with factor t^{C · ddim(X)}; reason: the standard meaning of the O; one absolute constant for every t ≥ 32
--   - reading: n log ∆ → n · L with L = ⌈log₂ ∆⌉ + 4; reason: the page's "L = ⌈log ∆⌉ + 4 = O(log ∆)" (p.12); the algorithm walks L + 1 levels, and n log ∆ itself tends to 0 as ∆ ↓ 1, so it cannot bound the steps there; the two agree up to a constant once ∆ ≥ 2
--   - reading: "computes … a collection Ψ" and "Φ … can be constructed in time" → one program writes both: the pairs of an output Ψ of some run of Algorithm 1, and explicit lists of the balls of Φ, shared between pairs; reason: the page constructs Φ from Ψ with one ball per net point (p.55); the two clauses have the same bound, so one run with that bound gives both
--   - reading: an algorithm on the unit-cost model → a program of DoublingMST.Machine, one fixed list of instructions, time = executed instructions; reason: Definition 2.1 is the paper's model (Section 1.1, p.2)
--   - encoding: a net hierarchy given as input, each net point storing pointers to its children (p.13) → EncodesHierarchy: records of label, level, one spare field, child count and child addresses, in integer memory; t in r[0], n in p[0], the root address in p[1]; reason: the page fixes no layout; the records hold the page's data plus one spare field, and reveal no distance
--   - encoding: the output collections Ψ and Φ → ListsPairCover: a count and six cells per pair in integer memory at negative addresses; reason: the page fixes no layout
--   - encoding: oracle given two point labels → an oracle call on a non-label integer leaves the run stuck; reason: excludes an undefined case
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 3.3, pp.14–15 (PDF pp.16–17); proof pp.53–55 (PDF pp.55–57)

import Mathlib
import Definitions.Def_DoublingMST_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_IsAlg1Output
import Definitions.Def_DoublingMST_EncodesHierarchy
import Definitions.Def_DoublingMST_ListsPairCover
open scoped Classical

namespace DoublingMST

/-- **Lemma 3.3, the running-time clauses (Algorithm 1 and Φ on the machine of Definition 2.1).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 3.3, pp.14–15 (PDF pp.16–17): "There is an algorithm that, given as input a metric
space (X, d) with ddim(X) ≤ ddim and minimum interpoint distance greater than 1 and diameter ∆, a net
hierarchy N over X as in Section 2.1, and a parameter t ≥ 32, computes in t^{O(ddim)}n log ∆ time a
collection Ψ of pairs of net points" … "Φ = {(B(u, 2^{lev(u)}), B(v, 2^{lev(v)})) : (u, v) ∈ Ψ} is a
t-WSPC of X, and it can be constructed in time t^{O(ddim)}n log ∆." The clauses (1)–(5) are the
companion item `DoublingMST.lemma_3_3`, which holds for every output `Ψ` below.

There are a program `P` and an absolute `C > 0` such that, under the standing assumptions of §2.1,
for every net hierarchy `H` laid out in integer memory, every `t ≥ 32`: started on that memory with
`t` in a real register and oracle `d`, the program halts within `t^{C·ddim(X)} · n · L` steps,
having written in integer memory an output `Ψ` of Algorithm 1 on `H` with parameter `t`, together
with the explicit balls of `Φ`.

**Formalization Note.** `log ∆` is read as `L = ⌈log ∆⌉ + 4`, the page's "L = ⌈log ∆⌉ + 4 = O(log ∆)"
(p.12): the algorithm walks `L + 1` levels, and `n log ∆` itself tends to `0` as `∆ ↓ 1`. The two
agree up to a constant once `∆ ≥ 2`. The memory layouts are `EncodesHierarchy` and `ListsPairCover`;
the program does not get `ddim`. -/
theorem lemma_3_3_time : ∃ P : Program, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ ι : Fin n → ℤ, Function.Injective ι →
    ∀ d : Fin n → Fin n → ℝ, IsMetric d → MinDistGtOne d →
    ∀ (H : NetHierarchy d) (t : ℝ), 32 ≤ t → ∀ (a₀ : ℤ) (mem : ℤ → ℤ), EncodesHierarchy H ι a₀ mem →
      ∃ k : ℕ, (k : ℝ) ≤ t ^ (C * ddim d) * n * (topLevel d : ℝ) ∧
        (run P ι d (initHierarchy n t a₀ mem) k).halted = true ∧
        ∃ Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ)), IsAlg1Output H t Ψ ∧
          ListsPairCover d ι Ψ (run P ι d (initHierarchy n t a₀ mem) k).integerMemory := by sorry

end DoublingMST
