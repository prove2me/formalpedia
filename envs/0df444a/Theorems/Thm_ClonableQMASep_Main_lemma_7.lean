-- Prove2me | Theorems.Thm_ClonableQMASep_Main_lemma_7
-- name    : ClonableQMASep.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:23.282273+00:00
-- url     : https://prove2.me/theorems/84411106-8819-4fce-856b-f2b056fe7739
-- title:
--   Lemma 7 — guessers from QCMA verifiers
-- statement:
--   Fix a code $C\subseteq\Sigma^n$, a target length $\ell\le n$, an injective $\mathsf{BinEnc}:[n]\times\Sigma\to\{0,1\}^\ell$ and a set $G$ of hash families (in the paper $G=\mathsf{Good}$). Suppose a quantum verifier $A$ takes a $t$-bit classical witness, makes at most $Q\ge1$ queries to the oracle $M[H,E]$, and satisfies completeness ($\ge2/3$ for some witness) on every YES instance and soundness ($\le1/3$ for every witness) on every NO instance of the self-encrypted CISS problem. Then for every integer $1\le L\le\lfloor n|\Sigma|/3\rfloor$ there is a query-free algorithm $\mathsf{Guesser}(1^L)$, fixed independently of $H$, such that every $H\in G$ has some $w_H\in\{0,1\}^t$ with
--   $$\Pr_{T\leftarrow\mathsf{Guesser}(1^L,w_H)}[\mathsf{Valid}_H(T)]\ge\Big(\frac1{72Q^2}\Big)^L ,$$
--   where $\mathsf{Valid}_H(T)$ means the $L$ pairs $(z_j,c^{(j)})$ are distinct, $c^{(j)}\in C$ and $H(c^{(j)})=z_j\|0^{n-\ell}$.
--
--   Together with Lemma 3 this rules out short classical witnesses for the CISS problem.
--
--   Differences from the source:
--
--   - generalization: Σ = F_q^s, the code C_λ and G = Good at parameter λ → any finite alphabet, any code set C, any set G of hash families; reason: the proof uses only that M[H] is a YES instance and M[H, E_{r−1}] a NO instance for H ∈ G; specializes to the paper's instance
--   - encoding: a quantum verifier with t-bit classical witness and at most Q queries → query algorithm on (i, x, c) × (ℤ/2)² × ({0,1}^t × Aux), initial |x₀, 0, (w, a₀)⟩, final projector, answers ⊥, 0, 1 coded 00, 01, 10 and XORed; reason: §2.2 query model and the execution V_Q M ⋯ M V_0|w, 0⟩ of p. 26; footnote 6
--   - encoding: a query-free algorithm Guesser(1^L) fixed independently of H → a kernel from witnesses to sub-probability distributions on L-tuples, chosen before H; reason: outputs with fewer than L pairs fail (footnote 5)
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), Lemma 7, p. 26 (proof pp. 26–28, Figure 4)

import Definitions.Def_ClonableQMASep_Main_Hash
import Definitions.Def_ClonableQMASep_Main_QueryModel

set_option autoImplicit false

namespace ClonableQMASep.Main

/-- Lemma 7 (Guessers from QCMA verifiers, p. 26). Fix an instance size: a code `C ⊆ A^n`, a
target length `ℓ ≤ n`, an injective `BinEnc : [n] × A → {0,1}^ℓ` and a set `G` of hash families.
Let `A` be a query verifier with a `t`-bit classical witness and at most `Q ≥ 1` queries to the
oracle `M[H, E]` (answers `⊥, 0, 1` encoded as `00, 01, 10`, accessed by XOR) that is complete
(`≥ 2/3`, some witness) on every YES instance and sound (`≤ 1/3`, every witness) on every NO
instance of the self-encrypted CISS problem with hash set `G`. Then for every integer
`1 ≤ L ≤ ⌊n|A|/3⌋` there is a query-free guesser, fixed independently of `H`, such that every
`H ∈ G` has a witness `w_H` with `Pr_{T ← Guesser(1^L, w_H)}[Valid_H(T)] ≥ (1/(72Q²))^L`. -/
theorem lemma_7 {n ℓ t : ℕ} {A Aux : Type} [Fintype A] [DecidableEq A] [Fintype Aux]
    [DecidableEq Aux] (C : Set (Fin n → A)) (hℓ : ℓ ≤ n)
    (BinEnc : Fin n → A → (Fin ℓ → Bool))
    (hBinEnc : Function.Injective (fun ix : Fin n × A => BinEnc ix.1 ix.2))
    (G : Set (HashFam n A)) (Q : ℕ) (hQ : 1 ≤ Q)
    (V : QueryVerifier (Fin n × A × (Fin n → A)) (Fin 2 → ZMod 2) Aux t) (hT : V.alg.T ≤ Q)
    (hcomp : ∀ M ∈ cissYes C BinEnc G, ∃ w, (2 : ℝ) / 3 ≤ V.acceptProb (queryFn M) w)
    (hsound : ∀ M ∈ cissNo C BinEnc G, ∀ w, V.acceptProb (queryFn M) w ≤ (1 : ℝ) / 3) :
    ∀ L : ℕ, 1 ≤ L → L ≤ n * Fintype.card A / 3 →
      ∃ Gs : (Fin t → Bool) → (Fin L → (Fin ℓ → Bool) × (Fin n → A)) → ℝ, IsGuesser Gs ∧
        ∀ H ∈ G, ∃ w, (1 / (72 * (Q : ℝ) ^ 2)) ^ L ≤ guessProb Gs w (ValidPad C H) := by sorry

end ClonableQMASep.Main
