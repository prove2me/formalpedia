-- Prove2me | Theorems.Thm_DynOracleConn_probe_simulation
-- name    : DynOracleConn.probe_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:11.779339+00:00
-- url     : https://prove2.me/theorems/4d1fc7ad-dcfe-4abd-86da-22cca56d2d14
-- title:
--   §3.1.2, p.21 — each adjacency probe of an epoch graph is answered by at most one PPHP probe
-- statement:
--   Consider one of the two graphs an epoch's probes see: $\mathcal G_n(\pi,z)$, or $\mathcal G_n(\pi,z)+\{t,v^0_i\}$ with $i$ known. For every pair of vertices $a,b$ there are at most one PPHP probe $o$ and a decoding map $f$, **both independent of $(\pi,z)$**, such that $\mathrm{Adjacent}(a,b)$ equals $f$ applied to the reply of $o$ under $P_X$.
--
--   The pairs that need a probe are $\{l^b_j,u^{b'}_i\}$, an edge iff $\pi(i)=j$ and $z_j=b\oplus b'$, and $\{v^b_i,r^b_j\}$, an edge iff $\pi(i)=j$. All other pairs have answers fixed by the construction.
--
--   **Formalization Note** $o=$ `none` means no PPHP probe is made. The graphs of the insertion phase are not covered: in the reduction those probes are answered in preprocessing, which sees $X$.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: d = ⌊(n−2)/8⌋ and one vertex layout → any injection e of the named vertices into Fin n; reason: the paper's layout is one such injection
--   - encoding: a trivial answer, or the single oracle probe P_X(i, j) → an optional probe o and a decoding map f, independent of (π, z); reason: the same dichotomy, with "the algorithm knows" made explicit as independence from X
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1.2, p.21

import Mathlib
import Definitions.Def_DynOracleConn_Gadget

namespace DynOracleConn

/-- **§3.1.2, p.21 — one PPHP probe per adjacency probe.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1.2, p.21: "since all
vertices and fixed edges are known, every probe has a trivial answer except for the six pairs
{lᵇⱼ, u^{b′}ᵢ} and {vᵇᵢ, rᵇⱼ} of an item i and a slot j, for b, b′ ∈ {0, 1}. … Hence, each such
probe can be answered by the single oracle probe P_X(i, j)."

For every epoch graph (𝒢ₙ(π, z), or 𝒢ₙ(π, z) plus `{t, v⁰ᵢ}` with `i` known) and every pair
`a, b` of vertices there are at most one PPHP probe `o` and a decoding map `f`, both independent of
`X`, such that `Adjacent(a, b)` equals `f` applied to the reply of `o`.

**Formalization Note.** The graphs of the insertion phase are not covered: there the edges are
announced as updates, and in the reduction those probes are answered in preprocessing, which
sees `X`. `o = none` means no PPHP probe is made. -/
theorem probe_simulation {n d : ℕ} (e : GV d ↪ Fin n) (i : Option (Fin d)) (a b : Fin n) :
    ∃ (o : Option (Fin d × Fin d)) (f : Option (Option Bool) → Bool),
      ∀ X : PPHPInst d, ((epochGraph e X i).Adj a b ↔ f (o.map (pOracle X)) = true) := by sorry

end DynOracleConn
