-- Prove2me | Theorems.Thm_APSCounting893_Main_trailing_query_builder_correct
-- name    : APSCounting893.Main.trailing_query_builder_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:48:23.761676+00:00
-- url     : https://prove2.me/theorems/e7016f7a-3917-4732-a6fa-4773815f0466
-- title:
--   Exact coefficient-query construction by the finite verifier
-- statement:
--   Fix $k$ parameter variables and one of the verifier's three query-building blocks. Let $x$ be the input word, $e$ its requested full exponent, and $q$ the requested numerator-bit index. Suppose the program starts at that block's entry, its four temporary buffers and selected query register are empty, the input prefix is $\operatorname{enc}(|x|)x$, and its source registers contain the canonical binary fields. In the final block the last exponent is required to be zero. If every exponent field has binary length at most $B$, the block reaches its prescribed successor with
--
--   $$\operatorname{query}=\operatorname{enc}(|x|)\,x\,\operatorname{encList}(e)\,\operatorname{enc}(\mathrm{numerator})\,\operatorname{enc}(q).$$
--
--   Every other register is preserved. Writing $b(q)$ for the binary length of $q$, $c_k=|\operatorname{enc}(k+1)|$, and $h(x)=|\operatorname{enc}(|x|)x|$, the number of register steps is bounded by
--
--   $$18b(q)+(k+1)(18B+9)+c_k+7h(x)+19.$$
--
--   This identity retains the original input delimiter, exponent-tuple count and requested bit. It is the query-construction component of the inner verifier in Lemma 6.5.
-- source:
--   Query-construction implementation for Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_TrailingVerifierProgram
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.trailing_query_builder_correct {k : ℕ} (A : Language) (q : TrailingQuery) (cfg : TrailingConfig k)
    (hs : cfg.state = .at (.build q .bitFirst) .entry) (ha : cfg.answer = none)
    (hc : TrailingClean cfg) (x : Word) (e : Fin (k + 1) →₀ ℕ) (bitIndex B : ℕ)
    (hbit : cfg.regs (trailingBitReg q) = bitIndex.bits.reverse)
    (hfields : ∀ i : Fin (k + 1), (q = .final ∧ i = Fin.last k) ∨
      cfg.regs (trailingFieldReg q i) = (e i).bits.reverse)
    (hzero : q = .final → e (Fin.last k) = 0)
    (hB : ∀ i, (e i).bits.length ≤ B)
    (hp : cfg.regs (trailingRegIndex .inputPrefix) = encodeNat x.length ++ x)
    (hq : cfg.regs (trailingQueryReg q) = []) :
    ∃ t ≤ 18 * bitIndex.bits.length + 9 + 4 + (1 + (k + 1) * (18 * B + 9)) +
        (encodeNat (k + 1)).length + 2 + 7 * (encodeNat x.length ++ x).length + 3,
      (trailingBaseProgram k).exec A cfg t =
        { state := .at (trailingAfterBuild k q) .entry,
          regs := Function.update cfg.regs (trailingQueryReg q)
            (coefficientQuery x e .numerator bitIndex), answer := none } := by sorry
