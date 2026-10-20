-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_lemma_1
-- name    : AtomicDynRouting.ResidenceTime.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:14.765241+00:00
-- url     : https://prove2.me/theorems/65c04f0c-df51-490c-b6fd-71eaba2fe350
-- title:
--   Lemma 1, p. 9 — token k departs every vertex v of Tk ∩ Gζ no later than r0 + (Loζdζ − Lvdζ + k − 1)
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, an integer time $r_0\ge r$, and the token process of §3.2 started at $r_0$. Write $L=L_{o_\zeta d_\zeta}$, and let $T_k$ be the motion trail of token $k$.
--
--   For every token $k\ge1$ and every vertex $v$ of $T_k\cap G_\zeta$, token $k$ departs from $v$ no later than
--   $$r_0+\bigl(L-L_{v d_\zeta}+k-1\bigr).$$
--
--   Here token $k$ departs from a vertex $v$ that is not the sink of $T_k\cap G_\zeta$ when it starts to move along the edge of $T_k\cap G_\zeta$ leaving $v$, and it departs from the sink when it reaches it.
--
--   Precisely: whenever token $k$ is in the buffer of an edge $e$ of $G_\zeta$ at some time $s_0$, it stays there until some time $s\ge s_0$ at which it leaves along $e$, with $s\le r_0+(L-L_{\operatorname{tail}(e) d_\zeta}+k-1)$; and if after that move it is no longer in a buffer of $G_\zeta$, then it reaches the sink $\operatorname{head}(e)$ at time $s+1\le r_0+(L-L_{\operatorname{head}(e) d_\zeta}+k-1)$.
--
--   Lemma 1 is the core of the multi-token technique. It holds for every run, with no condition on the later entrants.
--
--   **Formalization Note.** The conclusion is the predicate `DepartBound` of the Tokens file, with additive bounds ($s+L_{vd_\zeta}+1\le r_0+L+k$). Every vertex of $T_k\cap G_\zeta$ is the tail of one of its edges or its sink, so the two parts cover all of them; $T_k$ itself is not defined, as the buffers the token occupies are its trail.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, Lemma 1

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- Lemma 1, §3.2, p. 9. For every token `k ≥ 1` and every vertex `v` of `Tₖ ∩ Gζ`, token `k` departs from `v` no later than `r0 + (L_{oζdζ} − L_{vdζ} + k − 1)` (see `DepartBound`). -/
theorem lemma_1 {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (k : ℕ) (hk : 1 ≤ k) : DepartBound N R ζ r0 k := by sorry

end AtomicDynRouting.ResidenceTime
