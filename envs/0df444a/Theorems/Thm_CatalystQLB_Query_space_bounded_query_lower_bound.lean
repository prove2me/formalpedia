-- Prove2me | Theorems.Thm_CatalystQLB_Query_space_bounded_query_lower_bound
-- name    : CatalystQLB.Query.space_bounded_query_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:14.466594+00:00
-- url     : https://prove2.me/theorems/383fe1eb-9251-42d2-9c63-2ed64d4f6d15
-- title:
--   Lemma 8 — space-bounded query lower bound for $(x,f(g(x)))$ with $\lfloor c\lambda\rfloor$ catalysts (corrected: product catalyst state, strict threshold $c(1-h_2(p))<1$)
-- statement:
--   Let $f,g:\{0,1\}^\lambda\to\{0,1\}^\lambda$ be independent uniformly random functions, accessed through the XOR oracles $O_f,O_g$, and let $x\in\{0,1\}^\lambda$ be uniform. Let the catalyst register of $\ell$ qubits start in $\eta_{\ell,p}=((1-p)|0\rangle\langle0|+p|1\rangle\langle1|)^{\otimes\ell}$, and let $h_2$ be the binary entropy in bits.
--
--   Fix $c>0$ and $0\le p<1/2$ with
--   $$c\,\big(1-h_2(p)\big)<1.$$
--   Then there are constants $K$, $k$ and $a>0$, depending only on $c$ and $p$, such that for every $\lambda$, every $\ell\le\lfloor c\lambda\rfloor$ and every oracle circuit on the $2\lambda+\ell$ qubits $Q\otimes R\otimes C$ that makes $q$ queries to $O_f$ and $O_g$ in total:
--   1. the average probability that it maps $|x,0^\lambda\rangle\otimes\eta_{\ell,p}$ to a state with $|x,f(g(x))\rangle$ on the IO register is at most
--   $$K\,(q+1)^k\,2^{-a\lambda};$$
--   2. for every projector $\Pi^{\mathrm{dec}}$ on the $2\lambda+\ell$ qubits, the advantage with which the circuit followed by $\Pi^{\mathrm{dec}}$ distinguishes $|x,f(g(x))\rangle\otimes\eta_{\ell,p}$ from $|x,r\rangle\otimes\eta_{\ell,p}$, with $r$ uniform, is at most $K(q+1)^k2^{-a\lambda}$.
--
--   With $\lambda$ clean catalyst qubits three queries suffice (Lemma 73). The theorem says that with too little catalyst purity, measured by $\ell(1-h_2(p))<\lambda$, computing or even detecting $(x,f(g(x)))$ is exponentially hard for every polynomial-query algorithm. It is the query lower bound behind the paper's catalytic class separations.
--
--   **Formalization Note** The circuit's unitaries are fixed before $f$, $g$ and $x$ are drawn and act on exactly $2\lambda+\ell$ qubits; the catalyst need not be restored. `n` is the paper's $\lambda$; $2^{-a\lambda}$ is a real power.
--
--   Differences from the source:
--   - correction: $\eta_{\ell,p}:=(1-p)|0^\ell\rangle\langle0^\ell|+p|1^\ell\rangle\langle1^\ell|$ (Lemma 8's preamble) → the product state $((1-p)|0\rangle\langle0|+p|1\rangle\langle1|)^{\otimes\ell}$; reason: with the printed state the lemma is false: for $p=0.1$, $c=1.5$ ($c(1-h_2(p))\approx0.80$), $\ell=\lfloor1.5\lambda\rfloor$, CNOTs from catalyst qubit 1 onto the others map $|1^\ell\rangle$ to $|1,0^{\ell-1}\rangle$ and fix $|0^\ell\rangle$, leaving $\ell-1\ge\lambda$ clean qubits, and the three-query circuit of Lemma 73 then succeeds with probability 1; the paper uses the product state on p.7, in Theorem 117 and in §9
--   - correction: $c(1-h_2(p))\le1$ → $c(1-h_2(p))<1$; reason: at equality the lemma is false: with $\ell=\lfloor c\lambda\rfloor$, a catalyst permutation maps the at most $2^{\ell-\lambda}$ strings with $\mu_p(z)\ge2^{-(\ell-\lambda)}$ into $\{0^\lambda\}\times\{0,1\}^{\ell-\lambda}$, and the three-query circuit of Eq. (80) then succeeds with probability tending to $1/2$ by the central limit theorem (as in Remark 125), not $\mathrm{poly}(3)\,2^{-\Omega(\lambda)}$; Lemmas 119 and 121 assume the strict inequality
--   - generalization: $p\in(0,1/2)$ → $p\in[0,1/2)$; reason: at $p=0$ ($h_2(0)=0$, so $c<1$) it is the pure-catalyst bound of Lemmas 75 and 82 (Eqs. (51), (67)); it specializes to the source's range
--   - reading: $\mathrm{poly}(q)\cdot2^{-\Omega(\lambda)}$ → $\exists K,k,a>0$, depending only on $(c,p)$ and chosen before $\lambda$, $\ell$ and the circuit, with bound $K(q+1)^k2^{-a\lambda}$; reason: the standard meaning, uniform in $\lambda$, $\ell$ and the circuit; $(q+1)$ so that $q=0$ is covered
--   - reading: “makes $q$ queries” → $q$ = the total number of $O_f$ and $O_g$ gates; reason: the proofs count $q-1$ queries to $O_f$ and $q_g$ to $O_g$; either count gives the same statement up to the polynomial
--   - reading: “solves $\mathcal P$ with average success probability” → $\mathbb E_{f,g,x}\,\mathrm{tr}[(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes I_C)U(|x,0^\lambda\rangle\langle x,0^\lambda|\otimes\eta_{\ell,p})U^\dagger]$, with no condition on the final catalyst; reason: the preamble's “$|\psi\rangle$ is arbitrary” and Remark 79 (“even allowing for arbitrary errors”); averages as in Eq. (41)
--   - reading: “the distinguishing advantage in the decision variant of $\mathcal P$” → for every projector $\Pi^{\mathrm{dec}}$ on all $2\lambda+\ell$ qubits, the advantage $\mathrm{succ}_{\mathrm{dec}}(\eta_{\ell,p})$ of Eq. (102); reason: Lemma 121 applies $\Pi^{\mathrm{dec}}_\lambda$ to the whole $(n+\ell)$-qubit state; Lemma 82's $\Pi^{\mathrm{dec}}\otimes I_C$ is a special case
--   - reading: “any quantum algorithm with $\ell\le\lfloor c\lambda\rfloor$ auxiliary qubits” → any oracle circuit: fixed oracle-independent unitaries on exactly the $2\lambda+\ell$ qubits interleaved with $O_f\otimes I_C$ and $O_g\otimes I_C$, with no other workspace; reason: the paper's unitary model (p.3: “quantum unitary algorithms with at most $c\lambda$ auxiliary qubits”; p.43–44); a randomized choice of circuit is an average of fixed circuits and the bound is linear
--   - encoding: oracle queries on arbitrary wires → $O_f$, $O_g$ on the fixed wires $(Q,R)$; reason: an oracle on other wires differs by wire permutations, which are unitary gates of the circuit
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Lemma 8, p.12 (PDF 15); Lemmas 75, 82, 119, 121, pp.44–52, 72–76 (PDF 47–55, 75–79)

import Mathlib
import Definitions.Def_CatalystQLB_Query_forwardSuccess
import Definitions.Def_CatalystQLB_Query_decisionAdvantage
import Definitions.Def_CatalystQLB_Query_catalystState
import Definitions.Def_WildeQIT_binaryEntropy

namespace CatalystQLB.Query

open QAlgorithms

/-- **Lemma 8** (corrected), the space-bounded query lower bound (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), Lemma 8 and its preamble,
p.12 (PDF 15); the proofs are Lemmas 75, 82 (pp.44–52) and 119, 121 (pp.72–76)). Fix `c > 0`
and `0 ≤ p < 1/2` with `c (1 − h₂(p)) < 1`. There are constants `K`, `k` and `a > 0` such
that for every `n` (the paper's `λ`), every `ℓ ≤ ⌊cn⌋` and every oracle circuit on
`Q ⊗ R ⊗ C` (`2n + ℓ` qubits) making `q` queries to `O_f` and `O_g` in total:
1. the average probability that it maps `|x, 0^n⟩ ⊗ η_{ℓ,p}` to IO `= |x, f(g(x))⟩` is at most
   `K (q + 1)^k 2^{−an}`;
2. for every projector `Pdec` on the `2n + ℓ` qubits, its advantage in distinguishing
   `|x, f(g(x))⟩ ⊗ η_{ℓ,p}` from `|x, r⟩ ⊗ η_{ℓ,p}` is at most `K (q + 1)^k 2^{−an}`.

**Formalization Note** `η_{ℓ,p}` is the product state `catalystState` (Lemma 8's preamble prints
the two-string mixture, under which the lemma is false), and the threshold is strict (at
`c(1 − h₂(p)) = 1` the lemma is false). `poly(q)·2^{−Ω(λ)}` is read as `∃ K k a > 0`, chosen
before `n`, `ℓ` and the circuit, with `(q + 1)^k`. `h₂` is in bits; `2^{−an}` is a real power. -/
theorem space_bounded_query_lower_bound (c p : ℝ) (hc : 0 < c) (hp0 : 0 ≤ p) (hp : p < 1 / 2)
    (hcp : c * (1 - WildeQIT.binaryEntropy p) < 1) :
    ∃ (K : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧
      ∀ (n ℓ : ℕ), ℓ ≤ ⌊c * n⌋₊ → ∀ Circ : OracleCircuit n ℓ,
        forwardSuccess Circ (catalystState ℓ p) ≤
            K * ((Circ.numQueries : ℝ) + 1) ^ k * (2 : ℝ) ^ (-(a * n)) ∧
        ∀ Pdec : Matrix (Idx n ℓ) (Idx n ℓ) ℂ, Pdec.IsHermitian → Pdec * Pdec = Pdec →
          decisionAdvantage Circ Pdec (catalystState ℓ p) ≤
            K * ((Circ.numQueries : ℝ) + 1) ^ k * (2 : ℝ) ^ (-(a * n)) := by sorry

end CatalystQLB.Query
