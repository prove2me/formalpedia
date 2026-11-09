-- Prove2me | Theorems.Thm_DirTeleMC_theorem_1_1
-- name    : DirTeleMC.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:36:43.739134+00:00
-- url     : https://prove2.me/theorems/a4f9d231-df21-402e-8b17-37ca513eb7bc
-- title:
--   Theorem 1.1 — JUMPGREEDY runs in time $n^{O(\ell)}$ and returns a schedule of length $O(\ell^3\log k)(\mathrm{OPT}+k^{1/\ell})$
-- statement:
--   **Theorem 1.1.** There are absolute constants $c$ and $C$ such that for every integer $\ell \ge 2$ there is a function $\mathrm{alg}$, computed by a Turing machine in at most $(m+2)^{c\ell}$ steps on every input of length $m$ (so in time $n^{O(\ell)}$), with the following property. For every directed $k$-multicast instance $(G, s, K, k)$ with $K \subseteq V\setminus\{s\}$, all terminals reachable from $s$, and $2 \le k \le |K|$ (directed telephone multicast is the case $k = |K|$), the output of $\mathrm{alg}$ is a schedule $S$ returned by a run of JUMPGREEDY with parameter $\ell$; $S$ is valid, informs $k$ terminals, and
--   $$|S| \le C\,\ell^3 \ln k\,\left(\mathrm{OPT} + k^{1/\ell}\right),$$
--   where OPT is the length of any valid schedule informing $k$ terminals.
--
--   This is the paper's main result. Choosing $\ell$ gives an $O(k^\epsilon)$-approximation in polynomial time and an $O(\log^4 k)$-approximation in quasi-polynomial time (Corollary 1.2).
--
--   **Formalization Note** The constants are fixed before $\ell$ and the instance, the machine before the instance. Instances are encoded with their adjacency matrix, so the input length is at least $n^2$.
--
--   Differences from the source:
--   - reading: runs in n^{O(ℓ)} time → one Mathlib Turing machine (TM2ComputableInTime) per ℓ with time at most (m + 2)^{c·ℓ} on every input of length m, c fixed before ℓ; reason: the source names no machine model; one exponent constant uniform in ℓ is the meaning of n^{O(ℓ)}
--   - encoding: an instance of unstated input size → the encoding encInst with the n × n adjacency matrix, so n² ≤ m; reason: with this encoding (m + 2)^{O(ℓ)} and n^{O(ℓ)} are the same bound
--   - encoding: the deterministic algorithm JUMPGREEDY → a machine whose output on every well-formed instance is the output of a run of the relation JumpGreedyRun; reason: the relation leaves only the page's open ties open; the machine resolves them deterministically
--   - encoding: a DTM instance, and a directed k-multicast instance → one statement for well-formed k-multicast instances; reason: DTM is the case k = |K| of the same statement
--   - encoding: O(ℓ³ log k)(OPT + k^{1/ℓ}) → one absolute real C fixed before ℓ and the instance; natural logarithm; real power k^{1/ℓ}; reason: the meaning of the O-notation with constants independent of ℓ and the instance
--   - encoding: OPT, the minimum number of rounds of a feasible schedule → every valid schedule S′ informing k terminals; reason: the same claim without a minimum over a possibly empty set
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 1.1, p.1 (PDF p.2); restated p.19 (PDF p.20); proof p.31 (PDF p.32)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_JumpGreedyRun
import Definitions.Def_DirTeleMC_encInst

namespace DirTeleMC

/-- **Theorem 1.1** (JUMPGREEDY).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 1.1, p.1 (restated p.19, proved p.31): "For every integer ℓ ≥ 2, the deterministic algorithm
JUMPGREEDY with parameter ℓ runs in n^{O(ℓ)} time and, given a directed telephone multicast instance with k ≥ 2
terminals, returns a schedule of length O(ℓ³ log k)(OPT + k^{1/ℓ}). The same guarantee holds for directed
k-multicast, where k ≥ 2 is the number of terminals to be informed. In each case, OPT denotes the minimum number
of rounds required by a feasible schedule."

There are absolute constants `c` and `C` such that for every `ℓ ≥ 2` there is a function `alg`, computed by a
Turing machine in time at most `(m + 2)^{c·ℓ}` on every input of length `m`, such that on every well-formed
k-multicast instance (DTM is `k = |K|`) the output of `alg` is a schedule `S` returned by a run of JUMPGREEDY with
parameter `ℓ`, `S` is valid and informs `k` terminals, and its length is at most `C ℓ³ ln k (T′ + k^{1/ℓ})` for
every valid schedule of length `T′` that informs `k` terminals.

**Formalization Note.** Machine model: Mathlib's deterministic `Turing.TM2ComputableInTime` over the published
alphabet `Fin 4`, inputs encoded by `encInst` (with the `n × n` adjacency matrix, so the input length is at least
`n²`) and outputs by `encSched` (the source names no model). `c` and `C` are fixed before `ℓ` and the instance;
`alg` before the instance. OPT is written as "every valid schedule `S′` informing `k` terminals", so no minimum
over a possibly empty set is taken. `Real.log` is natural, `k^{1/ℓ}` the real power. -/
theorem theorem_1_1 :
    ∃ c : ℕ, ∃ C : ℝ, ∀ ℓ : ℕ, 2 ≤ ℓ → ∃ alg : Inst → List (List (ℕ × ℕ)),
      (∃ M : Turing.TM2ComputableInTime encInst encSched alg, ∀ m, M.time m ≤ (m + 2) ^ (c * ℓ)) ∧
      ∀ I : Inst, I.WF → ∃ S : Schedule I.n, alg I = S.toNat ∧ JumpGreedyRun ℓ I S ∧
        S.Valid I ∧ S.InformsK I ∧
        ∀ S' : Schedule I.n, S'.Valid I → S'.InformsK I →
          (S.length : ℝ) ≤
            C * (ℓ : ℝ) ^ 3 * Real.log I.k * ((S'.length : ℝ) + (I.k : ℝ) ^ ((1 : ℝ) / ℓ)) := by sorry

end DirTeleMC
