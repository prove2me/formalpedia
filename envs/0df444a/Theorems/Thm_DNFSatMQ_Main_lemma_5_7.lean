-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_5_7
-- name    : DNFSatMQ.Main.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:24.300327+00:00
-- url     : https://prove2.me/theorems/054a8bb2-7f1e-4621-ae72-a364faaec1fa
-- title:
--   Lemma 5.7 — path bound Pr[H_k fails] ≤ (s + s²|F|/|C⋆|)(3/4)^{⌈(k+1)/2⌉}
-- statement:
--   **Setting (§5.1).** $f = \bigvee_{c'\in T} c'$ for a set $T$ of at most $s$ noncontradictory terms, $F = f^{-1}(1)$, and $c_\star \in T$ is fixed, with satisfying set $C_\star$. The scan starts at $x\sim U_{C_\star}$ and uses an independent uniform permutation $\pi \in S_n$; $z_0 = x, z_1,\dots,z_n$ are its states and $I$ its rejected coordinates. For $c' \in T$, $K_{c'} = \mathrm{Fix}(c')\cap\mathrm{Free}(c_\star)$; $H_k$ is the event that each visited point satisfies some $c'\in T$ with $|K_{c'}|\le k$; $E_{c_\star} = |\mathrm{Fix}(c_\star)\setminus I|$ and $L_{c_\star} = |I\cap\mathrm{Free}(c_\star)|$.
--
--   For every integer $k\ge 0$, with $h_k = \lceil (k+1)/2\rceil$,
--   $$\Pr_{x,\pi}[H_k^c] \le \Big(s + s^2\frac{|F|}{|C_\star|}\Big)\Big(\frac34\Big)^{h_k},$$
--   and if $k\ge n$ then $H_k$ holds with probability one.
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: scan steps t = 1, …, n examine π(t) → steps t = 0, …, n−1 examine `π t`; `permRev π = π ∘ rev`; reason: 0-based indexing; same scan
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 5.7, p. 16 (PDF 17)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan

namespace DNFSatMQ.Main

/-- Lemma 5.7 (p. 16). -/
theorem lemma_5_7 {n s : ℕ} (T : Finset (Conj n)) (hT : T.card ≤ s) (cstar : Conj n)
    (hc : cstar ∈ T) (k : ℕ) :
    prob (withPerm cstar.unif) {p | ¬ eventH T cstar k p.1 p.2} ≤
        ((s : ℝ) + (s : ℝ) ^ 2 * ((unionSet T).card : ℝ) / cstar.cube.card) *
          (3 / 4 : ℝ) ^ ⌈((k : ℝ) + 1) / 2⌉₊ ∧
      (n ≤ k → prob (withPerm cstar.unif) {p | eventH T cstar k p.1 p.2} = 1) := by sorry

end DNFSatMQ.Main
