-- Prove2me | Theorems.Thm_EntangledPIR_Supplement_theorem_8_2
-- name    : EntangledPIR.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:29:16.950464+00:00
-- url     : https://prove2.me/theorems/f13673cc-1068-4ddd-9b7f-74be8596a2e8
-- title:
--   Theorem 8.2 — reduction to nondeterministic circuits
-- statement:
--   This theorem turns a protocol with short answers and small leakage into nondeterministic oracle circuits that accept the correct output too often.
--
--   Fix an oracle $O$, integers $n,b\ge1$ and a function $F:\{0,1\}^n\to\{0,1\}^b$. Fix also an $R$-bounded protocol in the model of Section 8, an initial state and strategies of the servers, and a set $S$ of colluding servers. There is an absolute constant $c_{\mathrm{rel}}>0$, the constant of (D.4), such that the following holds.
--
--   Put $N=2^n$ and $s_0=\lceil c_{\mathrm{rel}}R^2\rceil$. Suppose that, for reals $\gamma,D\ge0$, every relation $V$ on $\{0,1\}^n\times\{0,1\}^b$ computed by a nondeterministic oracle circuit of size at most $s_0$ satisfies
--   $$\bigl|\{x: V(x,F(x))\}\bigr|\le \gamma\,2^{-b}\sum_x\bigl|\{y:V(x,y)\}\bigr|+D. \tag{8.4}$$
--   Let $X$ be uniform on $\{0,1\}^n$, $C=\{Y=F(X)\}$, $\sigma=\Pr[C]$ and $M=\mathbb E[L\mathbf 1_C]$, where $L$ is the answer length of the servers outside $S$. Put
--   $$a=(1+n^{-2})\gamma,\qquad \beta=\frac{(1+n^{-2})(n^2D+1)}{N}.$$
--   Let $Q$ be a distribution of transcripts of $S$ and $\delta$ the distance (8.1) of the transcripts of $S$ from $Q$. Let $\imath(x;\tau)=\log(P_x(\tau)/Q(\tau))$ be the information density, with value $+\infty$ when $Q(\tau)=0<P_x(\tau)$. Then:
--
--   1. for every integer $0\le h<b$ and every real $\theta$,
--   $$\Pr[C,\ L\le h,\ \imath(X;T_S)\le\theta]\le a\,2^{h-b}+2^\theta\beta;$$
--   2. for every integer $0\le h<b$,
--   $$\Pr[C,\ L\le h]\le \delta+a\,2^{h-b}+\beta;$$
--   3. $M\ge\bigl(b(\sigma-\delta-\beta)-a(1-2^{-b})\bigr)_+$.
--
--   Combined with an oracle relative to which (8.4) holds (Proposition 8.1), this gives the lower bound of about $b$ bits on the answer length of every set of servers outside a set with small leakage, and hence the optimality of the factor two in Theorem 5.1 (Corollary 8.3).
--
--   **Formalization Note** The model is `EntangledPIR.Supplement.MultiServer` and the circuits are `EntangledPIR.Supplement.OracleCircuit`. $\log$ is base two. The constant $c_{\mathrm{rel}}$ is quantified before everything else.
--
--   Differences from the source:
--   - reading: the transcript T_S records all messages to and from S and "all timing information that they observe" → synchronous rounds with a public clock: every server's classical history, and T_S, has one entry per round (empty when the server receives no message), and its length records termination; reason: the source fixes only that messages are exchanged in rounds of a public schedule and that the observed timing includes abort and termination; the clock is the timing a round schedule provides, and the servers' instruments may use it, as they may use all their timing information
--   - reading: message-format conventions of App. A.1 → an answer that is not a codeword of its public code makes the client abort (output none); a run not stopped after the protocol's round bound T aborts; reason: A.1, p.53 ("aborts in a fixed way on a malformed message"), and D.2, p.61 ("every simulation in which all messages are validly encoded must terminate within the maximum transcript length")
--   - generalization: R-bounded (R bounds the advice length, ν and the transcript lengths, and the size of a circuit deciding Valid and computing Out and [L ≤ h] on canonical encodings of the transcripts) → ν ≤ R and some fixed-width encodings of the transcripts, injective where defined and defined on valid executions, with a circuit of size ≤ R that decides "valid and L ≤ h" and computes the output on such executions; reason: the proof (D.2–D.4) uses only these properties; a canonical encoding padded to fixed width is a special case, and the transcript lengths are bounded through the circuit's input wires; no advice-length bound is needed because the advice enters only through that circuit
--   - generalization: a classical client with advice that queries O classically; polynomially many servers that query the standard unitary oracle → the client is any function of (x, r, history), constrained only through the R-bounded circuit; any finite set of servers whose instruments are arbitrary and may depend on O; reason: every client and server of the source is of this form, so the source's protocols are a special case
--   - encoding: registers, fresh registers and instruments → one fixed finite register H_j per server containing its ancillas, with instruments in Kraus form (published EntangledPIR.Instrument) from H_j to H_j; reason: the initial state is arbitrary, so ancillas in |0⟩ are part of it, and an instrument into a larger register is an instrument on the enlarged register
--   - encoding: answers of any length → BitStr A with codewords shorter than A; reason: strings of length A stand for all longer answers, which the client rejects the same way (A.1)
--   - encoding: circuit size counts gates, wires, witness bits, query wires and fixed advice bits → it also counts the input wires and the output wires of the circuit, over the basis of fan-in-two AND/OR, NOT, constants and oracle gates; reason: the inputs and outputs are at most R by R-boundedness (the source's proof uses R ≥ ν + 10n and b ≤ R), so the sizes differ by a constant factor, which the existential c_rel absorbs
--   - encoding: ı(X; T_S) ≤ θ with ı = log₂(P_x(τ)/Q(τ)) and +∞ when Q(τ) = 0 < P_x(τ) → P_X(T_S) ≤ 2^θ Q(T_S); reason: on every transcript of positive probability the two events agree, including Q(τ) = 0
--   - encoding: Q a distribution of transcripts → a nonnegative function on all transcripts of S with HasSum Q 1; δ with the sum written as a tsum; reason: P_x has finite support, so the sums converge, and the value is the source's
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026), sha256 5cfce27c325365d29c042cf08ea41ddd83b9a5c0f711ef85e2620d8955251384, Theorem 8.2, p.43 (PDF p.45); model §2.1, p.10, §8, pp.40–41, App. A.1, p.53; c_rel from (D.4), p.62 (PDF p.64)

import Definitions.Def_EntangledPIR_Supplement_MultiServer

open Matrix
open Classical
open scoped ComplexOrder

namespace EntangledPIR

namespace Supplement

/-- **Theorem 8.2 (Reduction to Nondeterministic Circuits)**, Mantri, *Private Information Retrieval
from Two Entangled Servers*, manuscript (Nov. 2026), p.43 (PDF p.45).

There is an absolute constant `c_rel > 0` (that of (D.4), p.62) such that the following holds. Fix an
oracle `O`, integers `n, b ≥ 1`, a function `F : {0,1}^n → {0,1}^b`, an `R`-bounded protocol in the
model of Section 8, an initial state `ρ` and strategies of the servers, and a set `S` of colluding
servers. Put `N = 2^n`, `s₀ = ⌈c_rel R²⌉`, and suppose that for reals `γ, D ≥ 0` every relation `V` on
`{0,1}^n × {0,1}^b` computed by a nondeterministic oracle circuit of size at most `s₀` satisfies (8.4),
`|{x : V(x, F(x))}| ≤ γ 2^{-b} ∑_x |{y : V(x, y)}| + D`. Let `X` be uniform on `{0,1}^n`, `σ = Pr[C]`,
`M = E[L 1_C]`, `a = (1 + n^{-2})γ`, `β = (1 + n^{-2})(n²D + 1)/N`. Let `Q` be a distribution of
transcripts of `S`, `δ` the distance (8.1) and `ı(x; τ) = log(P_x(τ)/Q(τ))` (`+∞` when
`Q(τ) = 0 < P_x(τ)`). Then
1. for every integer `0 ≤ h < b` and real `θ`, `Pr[C, L ≤ h, ı(X; T_S) ≤ θ] ≤ a 2^{h−b} + 2^θ β`;
2. for every integer `0 ≤ h < b`, `Pr[C, L ≤ h] ≤ δ + a 2^{h−b} + β`;
3. `M ≥ (b(σ − δ − β) − a(1 − 2^{-b}))_+`.

**Formalization Note** The model is `MSProtocol`/`MSStrategy` (rounds of an adaptive schedule, any
finite set of servers with finite-dimensional registers and arbitrary instruments, public prefix-free
answer codes, abort on a non-codeword) and `RBounded` (encodings of the transcripts and a circuit of
size `≤ R` deciding validity with `L ≤ h` and computing the output). `C` is "the client outputs
`F(X)`". The event `ı(X; T_S) ≤ θ` is written `P_X(T_S) ≤ 2^θ Q(T_S)`, which is the same event on
every transcript of positive probability. `log` is base two, so `2^θ` is the real power. `Q` is any
nonnegative function with total mass one on the transcripts of `S`. `c_rel` is quantified first and
depends on nothing. -/
theorem theorem_8_2 :
    ∃ c_rel : ℝ, 0 < c_rel ∧
      ∀ (O : List Bool → Bool) (n b : ℕ), 1 ≤ n → 1 ≤ b → ∀ (F : Bits n → Bits b)
        (Srv : Type) [Fintype Srv] [DecidableEq Srv] (P : MSProtocol Srv n b) (S : Finset Srv)
        (R : ℕ), RBounded O P S R →
        ∀ (St : MSStrategy Srv P.A) (ρ : Matrix (Joint St) (Joint St) ℂ), ρ.PosSemidef →
        ρ.trace = 1 →
        ∀ (γ D : ℝ), 0 ≤ γ → 0 ≤ D →
        (∀ V : NondetCircuit n b, V.size ≤ ⌈c_rel * (R : ℝ) ^ 2⌉₊ →
          ((Finset.univ.filter fun x => V.Rel O x (F x)).card : ℝ) ≤
            γ * ((2 : ℝ) ^ b)⁻¹ *
                ∑ x : Bits n, ((Finset.univ.filter fun y => V.Rel O x y).card : ℝ) + D) →
        ∀ (Q : TransS S P.A → ℝ), (∀ τ, 0 ≤ Q τ) → HasSum Q 1 →
          (∀ h : ℕ, h < b → ∀ θ : ℝ,
              expCorrect P St ρ S F (fun x τ L =>
                  if L ≤ h ∧ transLaw P St ρ S x τ ≤ (2 : ℝ) ^ θ * Q τ then 1 else 0) ≤
                (1 + ((n : ℝ) ^ 2)⁻¹) * γ * (2 : ℝ) ^ ((h : ℤ) - b) +
                  (2 : ℝ) ^ θ * ((1 + ((n : ℝ) ^ 2)⁻¹) * ((n : ℝ) ^ 2 * D + 1) / (2 : ℝ) ^ n)) ∧
          (∀ h : ℕ, h < b →
              expCorrect P St ρ S F (fun _ _ L => if L ≤ h then 1 else 0) ≤
                transDist P St ρ S Q + (1 + ((n : ℝ) ^ 2)⁻¹) * γ * (2 : ℝ) ^ ((h : ℤ) - b) +
                  (1 + ((n : ℝ) ^ 2)⁻¹) * ((n : ℝ) ^ 2 * D + 1) / (2 : ℝ) ^ n) ∧
          max ((b : ℝ) * (expCorrect P St ρ S F (fun _ _ _ => 1) - transDist P St ρ S Q -
                  (1 + ((n : ℝ) ^ 2)⁻¹) * ((n : ℝ) ^ 2 * D + 1) / (2 : ℝ) ^ n) -
                (1 + ((n : ℝ) ^ 2)⁻¹) * γ * (1 - ((2 : ℝ) ^ b)⁻¹)) 0 ≤
            expCorrect P St ρ S F (fun _ _ L => (L : ℝ)) := by sorry

end Supplement

end EntangledPIR
