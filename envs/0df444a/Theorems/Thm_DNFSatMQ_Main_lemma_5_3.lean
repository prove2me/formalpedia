-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_5_3
-- name    : DNFSatMQ.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:33.894778+00:00
-- url     : https://prove2.me/theorems/571a312f-a59e-4d70-abbf-a8fd36eeb5e9
-- title:
--   Lemma 5.3 — prefix maps of the scan are bijections of F; reversal is a measure-preserving involution with the same rejected coordinates
-- statement:
--   Let $F\subseteq\{0,1\}^n$ be nonempty, $g_i(z) = z^{\oplus i}$ if $z^{\oplus i}\in F$ and $z$ otherwise, $\Phi_{\pi,0}=\mathrm{id}_F$ and $\Phi_{\pi,r} = g_{\pi(r)}\circ\cdots\circ g_{\pi(1)}$ for a permutation $\pi\in S_n$. Let $\pi_{rev}(t) = \pi(n-t+1)$ and
--   $$R : F\times S_n \to F\times S_n,\qquad R(x,\pi) = (\Phi_{\pi,n}(x), \pi_{rev}).$$
--   Then: (a) every $\Phi_{\pi,r}$, $0\le r\le n$, is a bijection of $F$; (b) $R$ is a bijection of $F\times S_n$; (c) $R$ maps the law $U_F\times U_{S_n}$ to itself; (d) the scan of $R(x,\pi)$ visits the original path in reverse, $\Phi_{\pi_{rev},t}(\Phi_{\pi,n}(x)) = \Phi_{\pi,n-t}(x)$ for $0\le t\le n$; (e) it has the same set of rejected coordinates.
--
--   Reversal is what lets the analysis of rejected flips (Lemma 5.8) use the start distribution at the end of the scan.
--
--   Differences from the source:
--   - encoding: scan steps t = 1, …, n examine π(t) → steps t = 0, …, n−1 examine `π t`; `permRev π = π ∘ rev`; reason: 0-based indexing; same scan
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: F = f⁻¹(1) for the target DNF f, F ≠ ∅ → an arbitrary nonempty `Finset` F of points; reason: every subset of the cube is the satisfying set of a DNF (one full term per point), so the class is the same
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 5.3, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan

namespace DNFSatMQ.Main

/-- Lemma 5.3 (p. 15). -/
theorem lemma_5_3 {n : ℕ} (F : Finset (Pt n)) (hF : F.Nonempty) :
    (∀ (π : Equiv.Perm (Fin n)) (r : ℕ), r ≤ n → Set.BijOn (scanPrefix F π r) ↑F ↑F) ∧
    Set.BijOn (fun p : Pt n × Equiv.Perm (Fin n) => (scanPrefix F p.2 n p.1, permRev p.2))
      ((↑F : Set (Pt n)) ×ˢ Set.univ) ((↑F : Set (Pt n)) ×ˢ Set.univ) ∧
    (withPerm (PMF.uniformOfFinset F hF)).map
        (fun p : Pt n × Equiv.Perm (Fin n) => (scanPrefix F p.2 n p.1, permRev p.2)) =
      withPerm (PMF.uniformOfFinset F hF) ∧
    (∀ x ∈ F, ∀ (π : Equiv.Perm (Fin n)) (t : ℕ), t ≤ n →
      scanPrefix F (permRev π) t (scanPrefix F π n x) = scanPrefix F π (n - t) x) ∧
    (∀ x ∈ F, ∀ π : Equiv.Perm (Fin n),
      rejected F (scanPrefix F π n x) (permRev π) = rejected F x π) := by sorry

end DNFSatMQ.Main
