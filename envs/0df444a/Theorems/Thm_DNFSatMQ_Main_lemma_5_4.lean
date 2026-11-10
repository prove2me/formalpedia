-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_5_4
-- name    : DNFSatMQ.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:25.817612+00:00
-- url     : https://prove2.me/theorems/3d0da142-1159-4d68-9a40-a20ec64e0aaa
-- title:
--   Lemma 5.4 — fixed-prefix counting bound Pr[Φ_{π,r}(x) ∈ A] ≤ |A|/|C⋆|
-- statement:
--   Let $f = \bigvee_{c'\in T} c'$ for a finite set $T$ of terms, $F = f^{-1}(1)$, and $c_\star \in T$ with satisfying set $C_\star \subseteq F$. For every permutation $\pi$, every $0\le r\le n$ and every $A \subseteq F$,
--   $$\Pr_{x\sim U_{C_\star}}[\Phi_{\pi,r}(x)\in A] = \frac{|\Phi_{\pi,r}(C_\star)\cap A|}{|C_\star|} \le \frac{|A|}{|C_\star|}.$$
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: §5 setup: T has at most s terms → T any finite set of terms (no bound s); reason: the lemma does not involve s; every finite T has |T| ≤ s for s = |T|
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 5.4, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan

namespace DNFSatMQ.Main

/-- Lemma 5.4 (p. 15). -/
theorem lemma_5_4 {n : ℕ} (T : Finset (Conj n)) (cstar : Conj n) (hc : cstar ∈ T)
    (π : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ n) (A : Finset (Pt n)) (hA : A ⊆ unionSet T) :
    prob cstar.unif {x | scanPrefix (unionSet T) π r x ∈ A} =
        ((cstar.cube.image (scanPrefix (unionSet T) π r) ∩ A).card : ℝ) / cstar.cube.card ∧
      ((cstar.cube.image (scanPrefix (unionSet T) π r) ∩ A).card : ℝ) / cstar.cube.card ≤
        (A.card : ℝ) / cstar.cube.card := by sorry

end DNFSatMQ.Main
