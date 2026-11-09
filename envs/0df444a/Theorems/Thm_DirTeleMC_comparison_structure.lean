-- Prove2me | Theorems.Thm_DirTeleMC_comparison_structure
-- name    : DirTeleMC.comparison_structure
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:28.546198+00:00
-- url     : https://prove2.me/theorems/e1ca854b-51b4-423c-a20a-1b8f3cec0afa
-- title:
--   Display (1), p.25, and proof of Theorem 1.1, p.31 — the comparison jump arborescence
-- statement:
--   Let $(G, s, K, k)$ be a well-formed instance, $\ell \ge 2$, $\eta = 2\ell - 1$, $\rho = \lceil k^{1/\ell}\rceil$, and let $S$ be a valid schedule of length $\theta \le k - 1$ that informs $k$ terminals. Then:
--   1. (display (1)) for every $d^* \le \theta$, $\;(\ell - 1)\max\{d^*, \rho - 1\} + \rho \le \ell(\theta + \rho + 1)$;
--   2. there is a structure $J^*$ rooted at the root of $\mathcal U_{\eta,\theta}$ (root labelled $s$, depth at most $\eta$, path jumps with at most $\theta$ arcs) that covers at least $k$ terminals, has maximum load at most $\Lambda^* \le (\ell - 1)\max\{\theta, \rho - 1\} + \rho$ (the value of $\Lambda^*$ at the out-degree bound $d^* \le \theta$), hence at most $\ell(\theta + \rho + 1)$, and has positive loads on at most $1 + k\theta \le k^2$ vertices.
--
--   This is the structure $J'$ to which Lemma B.6 is applied in the proof of Theorem 1.1, with $\nu = k^2$.
--
--   Differences from the source:
--   - generalization: an optimal schedule, with θ = OPT < k → any valid schedule of length θ ≤ k − 1 informing k terminals; reason: an optimal schedule with OPT < k is such a schedule
--   - reading: Λ* = (ℓ − 1) max{d*, ρ − 1} + ρ and 1 + kh*, with d*, h* the out-degree and height of T* → the same expressions at d* = h* = θ; reason: T* is internal to the proof and not named by the statement; d*, h* ≤ θ, and both expressions are nondecreasing in d*, h*, which is how the page uses them (Λ* ≤ Λ, |V*| ≤ 1 + k(k − 1))
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), display (1), p.25 (PDF p.26); proof of Theorem 1.1, "The comparison jump arborescence", p.31 (PDF p.32)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_IsJumpArb
import Definitions.Def_DirTeleMC_rho

namespace DirTeleMC

/-- **Display (1) and the comparison jump arborescence** (proof of Theorem 1.1).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), p.25: "Apply Lemma 4.2 to the arborescence T* of an optimal schedule, pruned to the paths from s to the
terminals. Its out-degree is d* ≤ OPT and its height is h* ≤ OPT. Lemma 4.2 gives a jump arborescence, for
θ = OPT, as h* ≤ OPT, with Λ* := (ℓ − 1) max{d*, ρ − 1} + ρ ≤ ℓ(OPT + ρ + 1). (1) The loads of this jump
arborescence are positive only on vertices of T*, of which there are at most 1 + kh*."; p.31, "The comparison
jump arborescence": "As its depth is at most η and its jumps are paths of T* (Lemma 4.2), with at most h* ≤ θ
arcs, it is a structure rooted at the root of U_{η,θ}. It covers the k terminals of T*, and its maximum load is
at most Λ* ≤ Λ, as the chains change no load." … "Hence |V*| ≤ 1 + kh* ≤ 1 + k(k − 1) ≤ k²."

For a well-formed instance, `ℓ ≥ 2`, `η = 2ℓ − 1` and every valid schedule `S` of length `θ ≤ k − 1` that
informs `k` terminals: display (1) holds for every `d* ≤ θ`, and there is a structure `J*` rooted at the root of
`U_{η,θ}` (root label `s`, height `η`, path jumps of at most `θ` arcs) covering at least `k` terminals, with
maximum load at most `(ℓ − 1) max{θ, ρ − 1} + ρ` (the value of `Λ*` at the out-degree bound `d* ≤ θ`) and
hence at most `ℓ(θ + ρ + 1)`, and positive loads on at most `1 + kθ ≤ k²` vertices.

**Formalization Note.** The source uses an optimal schedule with `OPT < k`; the statement holds for every valid
schedule of length at most `k − 1` (`θ` is its length). `Λ*` is nondecreasing in `d*`, and the out-degree `d*`
and height `h*` of the schedule's arborescence are at most `θ`, so `Λ*` and `1 + kh*` are stated at `d* = h* = θ`. -/
theorem comparison_structure (I : Inst) (hI : I.WF) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (S : Schedule I.n)
    (hS : S.Valid I) (hSk : S.InformsK I) (hlen : S.length ≤ I.k - 1) :
    (∀ d ≤ S.length,
      (ℓ - 1) * max d (rho I.k ℓ - 1) + rho I.k ℓ ≤ ℓ * (S.length + rho I.k ℓ + 1)) ∧
    ∃ J : JTree I.n, J.label = I.s ∧ JTree.IsStructure I.adj S.length (2 * ℓ - 1) J ∧
      I.k ≤ (I.K ∩ JTree.cov (2 * ℓ - 1) J).card ∧
      J.maxLoad ≤ (ℓ - 1) * max S.length (rho I.k ℓ - 1) + rho I.k ℓ ∧
      J.maxLoad ≤ ℓ * (S.length + rho I.k ℓ + 1) ∧
      (Finset.univ.filter fun v => 0 < J.loads v).card ≤ 1 + I.k * S.length ∧
      (Finset.univ.filter fun v => 0 < J.loads v).card ≤ I.k ^ 2 := by sorry

end DirTeleMC
