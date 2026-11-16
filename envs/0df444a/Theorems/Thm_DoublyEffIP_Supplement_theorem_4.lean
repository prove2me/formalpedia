-- Prove2me | Theorems.Thm_DoublyEffIP_Supplement_theorem_4
-- name    : DoublyEffIP.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:32.118138+00:00
-- url     : https://prove2.me/theorems/971948f3-9507-49e0-b727-48df3fb2a4d5
-- title:
--   Theorem 4 — $2^{-\sigma}$-sound IPP with row reduction, $|Q|\le\lceil 24\sigma k/d\rceil$ (corrected: $k,d,L\ge 1$)
-- statement:
--   There is a constant $c>0$ such that for every log-space uniform family of implementation circuits (a generator $T_\Phi$) there are a protocol, a $p$-space uniform generator $T_Q$ and a log-space uniform generator $T_\Psi$ for its outputs, and constants $C_{\mathrm{GKR}}>0$ and $K$ such that the following holds. Let $\sigma,d,k,L\in\mathbb N$ with $k,d,L\ge 1$, let $\mathbb F$ be a finite field (given by a presentation $\mathbb F_p[X]/(f)$), and let $\langle\Phi\rangle$ be a description of a predicate $\Phi:\mathbb F^{k\times L}\to\{0,1\}$ whose implementation circuit $C$ has size $S$ and depth $D$. Suppose
--
--   $$
--   d\ge 48\,\sigma\log_2 k,\qquad |\mathbb F|\ge C_{\mathrm{GKR}}\cdot 2^{\sigma+4c+7}\Big(\big(\sigma dL\log_2(|\mathbb F|(k+1))\big)^c+D\log_2 S+1\Big).
--   $$
--
--   Then the protocol, with public parameters $[\sigma,\mathbb F,\langle\Phi\rangle,d]$ and input matrix $M\in\{0,1\}^{k\times L}$, is a $2^{-\sigma}$-sound IPP with row reduction whose output set satisfies $Q\subsetneq[k]$ and
--
--   $$
--   |Q|\le\Big\lceil\frac{24\sigma k}{d}\Big\rceil .
--   $$
--
--   Writing $\tilde O(X)=K\cdot X\cdot\log_2(|\mathbb F|+k+L+2)^K$ (omitting $\mathrm{polylog}(|\mathbb F|,k,L)$ factors) and $\mathrm{poly}(d)=K(d+1)^K$, its complexities are:
--
--   1. $\ell=\tilde O(D\log S)$;
--   2. $a=\tilde O(dL+\mathrm{poly}(d))$;
--   3. $\mathrm{Ptime}\le K\,(k+L+d+S+\log_2|\mathbb F|+1)^K$, i.e. $\mathrm{poly}(k,L,d,S,\log|\mathbb F|)$;
--   4. $\mathrm{Vtime}=\tilde O\big(dL(D\log S+|\langle\Phi\rangle|)+\mathrm{poly}(d)\big)$;
--   5. $|\langle Q\rangle|=\tilde O(\mathrm{poly}(d))$ and $|\langle\Psi\rangle|=\tilde O(L+\mathrm{poly}(d))$;
--   6. the implementation circuits $G$ of $Q$ and $C_\Psi$ of $\Psi$ satisfy $\mathrm{size}(G)=\tilde O(\mathrm{poly}(d))$, $\mathrm{depth}(G)=\tilde O(1)$, $\mathrm{size}(C_\Psi)=\tilde O(|Q|\cdot L)$, $\mathrm{depth}(C_\Psi)=\tilde O(1)$.
--
--   The IPP with row reduction reduces checking a predicate on a whole matrix to checking a predicate on a small set of its rows; it is the step of the batch protocol that shrinks the number of transition claims.
--
--   **Formalization Note** The hypotheses are the theorem's "specific requirements" (its $\Omega$-conditions with explicit constants), with $C$ the implementation circuit of $\Phi$. All constants are chosen after the generator $T_\Phi$ and before $\sigma,d,k,L,\mathbb F,\langle\Phi\rangle$.
--
--   Differences from the source:
--   - correction: for all σ, d, k, L ∈ N → k ≥ 1, d ≥ 1 and L ≥ 1; reason: k = 0: log₂ 0 is undefined and Q ⊊ [0] is impossible, so with Φ ≡ 1 no protocol is complete; d = 0 (allowed when k = 1 or σ = 0): ⌈24σk/0⌉ is undefined, and the statement fails for k = L = σ = 1, Φ(M) = [M = 0], M = (1), which is 0-far from L_Φ while a prover replaying the honest answers for (0) makes V output Ψ with Ψ() = 1 (Q = ∅ as k = 1); L = 0: Vtime = Õ(poly(d)) does not depend on |⟨Φ⟩|, yet Φ() may be the last bit of ⟨Φ⟩ (take k = d = σ = 1 and the log-space generator whose circuit outputs input wire n + B − 1); for |⟨Φ⟩| beyond the time bound V cannot tell the satisfiable description from the unsatisfiable one, and a prover replaying the honest answers breaks soundness. For L ≥ 1, d ≥ 1 the Vtime bound contains dL|⟨Φ⟩| ≥ |⟨Φ⟩|
--   - reading: There exists a constant c > 0 such that for all … any description ⟨Φ⟩ of a predicate Φ with implementation circuit C → c > 0 is chosen first, uniformly over all Φ; then the uniform generator T_Φ of Φ's implementation circuits is fixed; the protocol, C_GKR and the Õ constant K exist after it and before σ, d, k, L, F, ⟨Φ⟩; reason: c is printed before Φ (it is the constant of the PVAL row-reduction protocol, Lemma 4); Definition 3 makes the generating machine fixed, and C_GKR (Theorem 3, stated for a given circuit family) and the O-constants may depend on it
--   - reading: d = Ω(σ log k); |F| = Ω(2^σ((σdL log(|F|k))^c + D log S)); 'the specific requirements on d and |F|' → the specific requirements: d ≥ 48σ log₂ k and |F| ≥ C_GKR·2^{σ+4c+7}((σdL log₂(|F|(k+1)))^c + depth(C) log₂ size(C) + 1), with C the implementation circuit of Φ and C_GKR > 0 existential; reason: the theorem gives these as the precise requirements; the Ω form 'D log S' identifies C as Φ's circuit; C_GKR is the unpinned constant of the cited GKR theorem
--   - reading: Õ omits polylog(|F|, k, L) factors; poly(·) → Õ(X) ≤ K·X·(log₂(|F|+k+L+2))^K and poly(·) = K(·+1)^K, one K for every bound; reason: the standard reading of Õ and poly with one universal constant; +2 and +1 avoid log 0 and 0^K
--   - reading: a field F → any finite field given by a presentation F_p[X]/(f), p prime, f monic irreducible (published AvgCaseTI.FieldPres), written in pp; |F| = p^{deg f}; reason: Definition 1: fields are constructible; every finite field has such a presentation
--   - reading: Φ a predicate F^{k×L} → {0,1} described by ⟨Φ⟩ → the hypothesis that C(M, ⟨Φ⟩) ∈ {0, 1} for every M ∈ F^{k×L}; L_Φ = {M | C(M, ⟨Φ⟩) = 1}; reason: Definition 9 takes Φ : F^{k×L} → {0,1}
--   - encoding: Q ⊂ [k] described by ⟨Q⟩ (Definition 4), G : [|Q|] × {0,1}^B → {0,1}^p → output word ⟨m⟩⟨Q⟩⟨Ψ⟩ with m = |Q|; rows 0-based, written as p-bit strings with p = ⌈log₂ k⌉; G a GF(2) circuit (gen read as 0); Q ⊊ [k] as distinct s_i < k and m < k; reason: m is the first shape parameter of G (Definition 4); Boolean gates are GF(2) gates up to constant factors (Remark 2)
--   - encoding: M ∈ {0,1}^{k×L}, Δc-ball over F → M : Fin k → Fin L → Bool embedded by 0, 1; d-far: no M' over F with every column differing in at most d rows satisfies Φ; reason: Definition 2
--   - encoding: public parameters [σ, F, ⟨Φ⟩, d] → pp = ⟨σ⟩⟨F⟩⟨d⟩⟨k⟩⟨L⟩⟨Φ⟩ in self-delimited binary, with the shape (k, L) of the input matrix; reason: the verifier receives no input but must know the matrix shape its output refers to
--   - encoding: a Turing machine (prover, verifier); V probabilistic → published multitape PrimitiveMachine; V a deterministic machine run on (queries, answers, pp), halting within Vtime on every query and answer sequence; reason: the paper fixes no model; public coins and 'V never rejects in the middle of an execution'
--   - encoding: uniform circuit families generated by a fixed O(f)-space Turing machine → the published TreeEdgeRankPC.Transducer (read-only input, one work tape, write-only output) with work space c·(f+1), c one constant per family; reason: the standard space-bounded transducer model; O(f) with one constant per family
--   - encoding: arithmetic circuits of fan-in 2 ADD and MULT gates; descriptions ⟨·⟩; size and depth → Circuit: gates add/mul/const 0,1/gen (field generator α), wires numbered inputs first; encCircuit; size = number of gates; depth = longest input-output path; reason: constants are needed for any non-homogeneous predicate (e.g. ⊤ outputs 1); gen gives every field constant
--   - encoding: Pr over the verifier's coins q ←R {0,1}^a; Pr = 1; Pr ≤ 2^{−σ} → counts over Fin ℓ → List.Vector Bool a: every q; #{q} · 2^σ ≤ 2^{ℓa}; reason: the coins are uniform, so the values are the same
--   - reading: completeness: there exists a prover strategy P; P is deterministic and runs in time Ptime → completeness by the protocol's own stateless next-message prover machine, whose running times over the ℓ rounds sum to at most Ptime on every input; reason: p.10 ('The machine P is deterministic and runs in time Ptime'); otherwise Ptime would bound nothing
--   - encoding: any (computationally unbounded) prover strategy P* → any function from the list of queries so far to an a-bit answer, chosen after the input; reason: the input and pp are fixed before P* is chosen; a randomized strategy is a mixture of deterministic ones
--   - reading: ℓ and a, numbers of the protocol → computed from pp by a parameter machine within Vtime steps; reason: the verifier must know ℓ and a; this keeps them from carrying advice
--   - reading: both parties have explicit access to pp (layout unspecified) → prover's word: x, round index, queries, then pp; verifier's word: queries, answers, then pp; all self-delimited; reason: the paper fixes no layout; with pp last neither party must scan parameters the time bounds do not charge for
--   - reading: the bounds on the output (|⟨Ψ⟩|, size and depth of its implementation circuit) → hold for every output ≠ ⊥ of the verifier, on every coin and answer sequence; reason: they are properties of what the verifier outputs, which it controls
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Theorem 4, Section 3.4.2, p.13 (restated pp.33–34; proof in Appendix A.4, pp.34–36)

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_evalCircuit
import Definitions.Def_DoublyEffIP_Supplement_circuitDepth
import Definitions.Def_DoublyEffIP_Supplement_IsImpl
import Definitions.Def_DoublyEffIP_Supplement_implShape
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_DoublyEffIP_Supplement_flatMat
import Definitions.Def_DoublyEffIP_Supplement_IsLogSpaceUniform
import Definitions.Def_DoublyEffIP_Supplement_IsSetSpaceUniform
import Definitions.Def_DoublyEffIP_Supplement_OProtocol
import Definitions.Def_DoublyEffIP_Supplement_IsSoundIPPRR
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **Theorem 4** (IPP with row reduction) — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.4.2, p.13 (restated p.33–34, proved
in Appendix A.4).

There is a constant `c > 0` such that for every log-space uniform family `TΦ` of implementation
circuits (Definition 5) there are a protocol, a `p`-space uniform family `TQ` (for `⟨Q⟩`), a
log-space uniform family `TΨ` (for `⟨Ψ⟩`) and constants `C_GKR > 0` and `K` such that: for all `σ, d, k, L`, every presented
finite field `F` and every description `⟨Φ⟩` whose implementation circuit `C` (of size `S` and
depth `D`) computes a predicate `Φ : F^{k×L} → {0,1}`, if `k, d, L ≥ 1`,
* `d ≥ 48 σ log₂ k`,
* `|F| ≥ C_GKR · 2^{σ+4c+7} ((σ d L log₂(|F|(k+1)))^c + D log₂ S + 1)`,

then the protocol is a `2^{-σ}`-sound IPP with row reduction for `M ∈ {0,1}^{k×L}` with
`|Q| ≤ ⌈24σk/d⌉` and, writing `Õ(X) = K · X · log₂(|F|+k+L+2)^K` and `poly(d) = K(d+1)^K`:
`ℓ = Õ(D log S)`, `a = Õ(dL + poly(d))`, `Ptime ≤ K(k+L+d+S+log₂|F|+1)^K`,
`Vtime = Õ(dL(D log S + |⟨Φ⟩|) + poly(d))`, `|⟨Q⟩| = Õ(poly(d))`, `|⟨Ψ⟩| = Õ(L + poly(d))`,
`size(G) = Õ(poly(d))`, `depth(G) = Õ(1)`, `size(C_Ψ) = Õ(|Q| · L)`, `depth(C_Ψ) = Õ(1)`.

**Formalization Note.** The hypotheses are the theorem's "specific requirements" (the Ω-conditions
with their constants), where `C` is `Φ`'s implementation circuit. `k ≥ 1` and `d ≥ 1` exclude the
undefined cases `log 0`, `Q ⊊ [0]` and `24σk/0`. `L ≥ 1` is a correction: at `L = 0` the printed
`Vtime = Õ(poly(d))` does not depend on `|⟨Φ⟩|`, yet the verifier must learn the constant `Φ()`, which
can be the last bit of `⟨Φ⟩` (see the item's notes). The constant `c` comes first, as printed ("There exists a constant
c > 0 such that for all … any description ⟨Φ⟩"; it is the constant of the PVAL row-reduction
protocol, Lemma 4, which does not depend on `Φ`). The generator `TΦ` of `Φ`'s circuits is fixed
next (Definition 3: "a fixed … Turing machine"); `C_GKR` (the constant of Theorem 3, stated for a
given circuit family) and the `Õ`/`poly` constant `K` are chosen after it and before
`σ, d, k, L, F, ⟨Φ⟩`. See `IsSoundIPPRR` for the protocol model. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (TΦ : Transducer) (cΦ : ℕ), IsLogSpaceUniform TΦ cΦ →
    ∃ (prot : OProtocol) (TQ TΨ : Transducer) (cQ cΨ : ℕ) (CGKR : ℝ) (K : ℕ),
      0 < CGKR ∧ IsSetSpaceUniform TQ cQ ∧ IsLogSpaceUniform TΨ cΨ ∧
      ∀ (σ d k L : ℕ) (P : AvgCaseTI.FieldPres) (descΦ : List Bool) (C : Circuit),
        1 ≤ k → 1 ≤ d → 1 ≤ L →
        IsImpl TΦ (implShape (k * L) descΦ.length) C →
        (∀ M' : Fin k → Fin L → P.F,
          evalCircuit (AdjoinRoot.root P.f) C (flatMat M' ++ bitsIn P.F descΦ) = [0] ∨
          evalCircuit (AdjoinRoot.root P.f) C (flatMat M' ++ bitsIn P.F descΦ) = [1]) →
        (d : ℝ) ≥ 48 * (σ : ℝ) * Real.logb 2 (k : ℝ) →
        (P.q : ℝ) ≥ CGKR * (2 : ℝ) ^ ((σ : ℝ) + 4 * c + 7) *
          (((σ : ℝ) * (d : ℝ) * (L : ℝ) * Real.logb 2 ((P.q : ℝ) * ((k : ℝ) + 1))) ^ c +
            (circuitDepth (k * L + descΦ.length) C : ℝ) * Real.logb 2 (C.gates.length : ℝ) + 1) →
        let D : ℝ := circuitDepth (k * L + descΦ.length) C
        let Sz : ℝ := C.gates.length
        let lg : ℝ := Real.logb 2 ((P.q : ℝ) + (k : ℝ) + (L : ℝ) + 2) ^ K
        let pd : ℝ := (K : ℝ) * ((d : ℝ) + 1) ^ K
        IsSoundIPPRR prot TQ TΨ σ P TΦ descΦ d k L
          ⌈((24 * σ * k : ℕ) : ℝ) / (d : ℝ)⌉₊
          ((K : ℝ) * (D * Real.logb 2 Sz) * lg)
          ((K : ℝ) * ((d : ℝ) * (L : ℝ) + pd) * lg)
          ((K : ℝ) * ((k : ℝ) + (L : ℝ) + (d : ℝ) + Sz + Real.logb 2 (P.q : ℝ) + 1) ^ K)
          ((K : ℝ) * ((d : ℝ) * (L : ℝ) * (D * Real.logb 2 Sz + (descΦ.length : ℝ)) + pd) * lg)
          ((K : ℝ) * pd * lg)
          ((K : ℝ) * ((L : ℝ) + pd) * lg)
          ((K : ℝ) * pd * lg)
          ((K : ℝ) * lg)
          (fun m => (K : ℝ) * ((m : ℝ) * (L : ℝ)) * lg)
          ((K : ℝ) * lg) := by sorry

end DoublyEffIP.Supplement
